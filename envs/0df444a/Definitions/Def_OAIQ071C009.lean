-- Prove2me | Definitions.Def_OAIQ071C009
-- name    : OAIQ071C009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T05:15:55.919394+00:00
-- url     : https://prove2.me/theorems/d9047049-c007-4aaa-9c6e-3ea1a13ea2e2
-- title:
--   Definitions bundle OAIQ071C009 of the split of OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 146 declarations of OpenAI's Lean: 38 definitions, 2 instances and 106 theorems. The definitions and types are `OAI.CoulombAtom.arrayObservationInformation`, `OAI.CoulombAtom.arrayObservedConfiguration`, `OAI.CoulombAtom.arrayUnorderedConfiguration`, `OAI.CoulombAtom.capBandStatistic`, `OAI.CoulombAtom.closedAnnularShell`, `OAI.CoulombAtom.conditionalRetainedFieldSum`, `OAI.CoulombAtom.densityLocalizationError`, `OAI.CoulombAtom.exteriorCoordinates`, `OAI.CoulombAtom.freshPatchMass`, `OAI.CoulombAtom.freshRadialTest`, `OAI.CoulombAtom.graphNuclearSum`, `OAI.CoulombAtom.innerPotential`, `OAI.CoulombAtom.localCountRatioSet`, `OAI.CoulombAtom.localCountSupremum`, `OAI.CoulombAtom.localDensityBudget`, `OAI.CoulombAtom.masterCenteredKernel`, `OAI.CoulombAtom.masterPosterior`, `OAI.CoulombAtom.masterTestConstant`, `OAI.CoulombAtom.observationGraphFactor`, `OAI.CoulombAtom.observedAnnularCount`, `OAI.CoulombAtom.observedLocalCount`, `OAI.CoulombAtom.physicalObservationEvent`, `OAI.CoulombAtom.physicalObservationProbability`, `OAI.CoulombAtom.posteriorTestValue`, `OAI.CoulombAtom.quantumEventProbability`, `OAI.CoulombAtom.quantumObservationEvent`, `OAI.CoulombAtom.rawAnnularMoment`, `OAI.CoulombAtom.smoothDerivativeProductL2`, `OAI.CoulombAtom.smoothMultiplyL2`, `OAI.CoulombAtom.symmetricArraySpace`, `OAI.CoulombAtom.weightedPatchLocalPotential`, `OAI.CoulombAtom.weightedPatchMass`, `OAI.CoulombAtom.weightedPatchTestAbs`, `OAI.CoulombAtom.weightedPatchTestSquare`, `OAI.CoulombBarrier.masterConfigurationDensity`, `OAI.CoulombBarrier.originalMasterField`, `OAI.CoulombBarrier.rawAnnularCount`, `OAI.CoulombBarrier.spatialGridIndex`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CoulombIonization_Fermionic_OccupationPairDensity`, `CoulombIonization_Fermionic_SlaterOccupation`, `CoulombIonization_Fermionic_SlaterRepulsion`, `CoulombIonization_FieldAnalysis_BarrierObservationTowerBarrier`, `CoulombIonization_FieldAnalysis_ConditionalObservables`, `CoulombIonization_FieldAnalysis_CoreFieldRegularity`, `CoulombIonization_FieldAnalysis_DeletedFieldBudget`, `CoulombIonization_FieldAnalysis_ObservedFieldScale`, `CoulombIonization_FormDomain_ActualMasterCenterComparison`, `CoulombIonization_FormDomain_BindingSums`, `CoulombIonization_FormDomain_BlockWedge`, `CoulombIonization_FormDomain_CoherentLimitInsertion`, `CoulombIonization_FormDomain_CosetWedge`, `CoulombIonization_FormDomain_FiniteFermionEnsemble`, `CoulombIonization_Ionization_ConditionalPatchMinimizer`, `CoulombIonization_Ionization_ConditionalPricedUpper`, `CoulombIonization_Ionization_PricedUpperComparison`, `CoulombIonization_Localization_ArraySymmetry`, `CoulombIonization_Localization_BarrierEventSymmetryBarrier`, `CoulombIonization_Localization_CoherentRealKinetic`, `CoulombIonization_Localization_ConditionalRetainedGap`, `CoulombIonization_Localization_ConditionalSandwich`, `CoulombIonization_Localization_CutOuterLaw`, `CoulombIonization_Localization_DyadicObservation`, `CoulombIonization_Localization_FreshPosteriorSandwich`, `CoulombIonization_Localization_Observation`, `CoulombIonization_Localization_ObservedAnnularCountBarrier`, `CoulombIonization_Localization_OriginalPosteriorKernel`, `CoulombIonization_Localization_PacketScale`, `CoulombIonization_Localization_PatchLocalObservable`, `CoulombIonization_Localization_PosteriorFreshTestBarrier`, `CoulombIonization_Localization_QuantumMultiplierLaw`, `CoulombIonization_Localization_UniformEventGraph`, `CoulombIonization_Localization_UnorderedObservations`, `CoulombIonization_RadialBounds_AnnularCellGeometryBarrier`, `CoulombIonization_RadialBounds_AnnularCutExcess`, `CoulombIonization_RadialBounds_BarrierMasterRegularityBarrier`, `CoulombIonization_RadialBounds_BarrierSpatialNetBarrier`, `CoulombIonization_RadialBounds_BarrierTruncationBarrier`, `CoulombIonization_RadialBounds_CellCountSupremumBarrier`, `CoulombIonization_RadialBounds_CellScaleBarrier`, `CoulombIonization_RadialBounds_FreshInnerCountsBarrier`, `CoulombIonization_RadialBounds_LocalOrdinaryBarrier`, `CoulombIonization_RadialBounds_RadialPatchGeometry`, `CoulombIonization_RadialBounds_RootMomentCauchyBarrier`, `CoulombIonization_RadialBounds_SharpFreshPatchBarrier`, `CoulombIonization_RadialBounds_SpatialCapSubmeanBarrier`, `CoulombIonization_RadialBounds_UnshiftedCellCountBarrier`, `CoulombIonization_ThomasFermi_ActualPatchCap`, `CoulombIonization_ThomasFermi_CoherentFiniteInsertion`, `CoulombIonization_ThomasFermi_ConditionalPatchPDE`, `CoulombIonization_ThomasFermi_CutMomentBounds`, `CoulombIonization_ThomasFermi_OutCutAntisymmetry`, `CoulombIonization_ThomasFermi_PatchRandomVariables`, `CoulombIonization_Variational_BindingBase`, `CoulombIonization_Variational_BlockEnergy`, `CoulombIonization_Variational_BlockSwap`, `CoulombIonization_Variational_CorrelatedFiniteInsertion`, `CoulombIonization_Variational_ExpectedTruncatedControl`, `CoulombIonization_Variational_IntegratedLipschitzControl`, `CoulombIonization_Variational_LocalWidthKernel`, `CoulombIonization_Variational_MasterRecovery`, `CoulombIonization_Variational_OccupationTraces`, `CoulombIonization_Variational_OutRetainedLower`, `CoulombIonization_Variational_SelectedPatchBudget`, `CoulombIonization_Variational_SpinSpaceIntegrable`.
--
--   **Imports.** It imports the published bundle `Def_CoulombIonization`; the bundles `OAIQ071C006` and `OAIQ071C007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ071C010`, `OAIQ071C013` and `OAIQ071C014`; the statements `OAI_CoulombAnalysis_weak_limit_identification`, `OAI.CoulombAtom.normalized_inner_event_global_bound`, `OAI.CoulombBarrier.original_finite_barrier_iteration` and `OAI_CoulombBarrier_selected_screened_profile`; the proofs of `OAI.CoulombAtom.actual_priced_particle_bound_three`, `OAI_CoulombBarrier_initial_barrier_invariant`, `OAI.CoulombBarrier.original_finite_barrier_iteration`, `OAI_CoulombBarrier_outward_barrier_invariant` and `OAI_CoulombBarrier_selected_screened_profile`.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C006
import Definitions.Def_OAIQ071C007

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CosetWedge
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped Topology BigOperators

namespace CoulombAtom

lemma SobolevVector.cosetWedgeTerm {n : ℕ} {T : FormVector n} (hT : SobolevVector T)
    (H : Subgroup (Equiv.Perm (Fin n))) (q : Equiv.Perm (Fin n) ⧸ H) :
    SobolevVector (cosetWedgeTerm H T q) :=
  (hT.reindex q.out.symm).scale _

lemma cosetWedge_fermion {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} {T : FormVector n}
    (hT : SobolevVector T) (hTa : SubgroupFermion H T) : SobolevFermion (cosetWedge H T) := by
  classical
  have hw := SobolevVector.sum (fun q => hT.cosetWedgeTerm H q)
  refine ⟨hw.1,hw.2.1,hw.2.2,?_⟩
  intro π s
  have hh (q : Equiv.Perm (Fin n) ⧸ H) : ∀ᵐ x,
      (cosetWedgeTerm H T q).value (s ∘ π) (x ∘ π) =
      (((Equiv.Perm.sign π : ℤ) : ℂ)) * (cosetWedgeTerm H T (π • q)).value s x := by
    let κ := (π • q).out⁻¹ * (π * q.out)
    have hk : κ ∈ H := by
      apply QuotientGroup.eq.mp
      exact (QuotientGroup.out_eq' (π • q)).trans
        (MulAction.Quotient.mk_smul_out H π q).symm
    have he : π * q.out = (π • q).out * κ := by simp [κ]
    have hp := (permuteConfiguration_preserving (π • q).out).quasiMeasurePreserving.ae
      (hTa κ hk (s ∘ (π • q).out))
    filter_upwards [hp] with x hx
    simp only [permuteConfiguration_apply] at hx
    have hsg : (((Equiv.Perm.sign π : ℤ) : ℂ)) *
        (((Equiv.Perm.sign q.out : ℤ) : ℂ)) =
        (((Equiv.Perm.sign (π • q).out : ℤ) : ℂ)) *
        (((Equiv.Perm.sign κ : ℤ) : ℂ)) := by
      have ht := congrArg (fun σ => (((Equiv.Perm.sign σ : ℤ) : ℂ))) he
      simpa only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul] using ht
    have hsg' : (((Equiv.Perm.sign q.out : ℤ) : ℂ)) *
        (((Equiv.Perm.sign κ : ℤ) : ℂ)) =
        (((Equiv.Perm.sign π : ℤ) : ℂ)) *
        (((Equiv.Perm.sign (π • q).out : ℤ) : ℂ)) := by
      have hs := complex_sign_sq (π • q).out
      have ht := complex_sign_sq q.out
      linear_combination -(((Equiv.Perm.sign (π • q).out : ℤ) : ℂ)) *
        (((Equiv.Perm.sign q.out : ℤ) : ℂ)) * hsg +
        (((Equiv.Perm.sign π : ℤ) : ℂ)) *
        (((Equiv.Perm.sign (π • q).out : ℤ) : ℂ)) * ht -
        (((Equiv.Perm.sign κ : ℤ) : ℂ)) *
        (((Equiv.Perm.sign q.out : ℤ) : ℂ)) * hs
    have hv : ((s ∘ π) ∘ q.out) = (s ∘ (π • q).out) ∘ κ := by
      change s ∘ (π * q.out) = s ∘ ((π • q).out * κ)
      rw [he]
    have hvx : ((x ∘ π) ∘ q.out) = (x ∘ (π • q).out) ∘ κ := by
      change x ∘ (π * q.out) = x ∘ ((π • q).out * κ)
      rw [he]
    rw [cosetWedgeTerm_value,cosetWedgeTerm_value,hv,hvx,hx,← mul_assoc,hsg',mul_assoc]
  have ha := (ae_all_iff.mpr hh)
  filter_upwards [ha] with x hx
  change (∑ q, (cosetWedgeTerm H T q).value (s ∘ π) (x ∘ π)) =
    _ * ∑ q, (cosetWedgeTerm H T q).value s x
  simp_rw [hx]
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (MulAction.toPerm π) (fun q => (cosetWedgeTerm H T q).value s x)

lemma formMass_cosetWedge {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} {T : FormVector n}
    (hT : SobolevVector T) (hd : FormsDisjoint (cosetWedgeTerm H T)) :
    formMass (cosetWedge H T) = (Fintype.card (Equiv.Perm (Fin n) ⧸ H) : ℝ) * formMass T := by
  rw [cosetWedge, formMass_sum_disjoint (fun q => hT.cosetWedgeTerm H q) hd]
  simp only [formMass_cosetWedgeTerm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma formEnergy_cosetWedge {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} {T : FormVector n}
    (hT : SobolevVector T) (hd : FormsDisjoint (cosetWedgeTerm H T)) (Z : ℝ) :
    formEnergy Z (cosetWedge H T) = (Fintype.card (Equiv.Perm (Fin n) ⧸ H) : ℝ) * formEnergy Z T := by
  rw [cosetWedge, formEnergy_sum_disjoint (fun q => hT.cosetWedgeTerm H q) hd]
  simp only [formEnergy_cosetWedgeTerm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem normalized_coset_wedge_trial {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} {T : FormVector n}
    (hT : SobolevVector T) (hTa : SubgroupFermion H T) (hm : formMass T = 1)
    (hd : FormsDisjoint (cosetWedgeTerm H T)) (Z : ℝ) :
    ∃ F : FormVector n, FormAdmissible F ∧ formEnergy Z F = formEnergy Z T := by
  have hw := formMass_cosetWedge hT hd
  rw [hm,mul_one] at hw
  have hp : 0 < formMass (cosetWedge H T) := by
    rw [hw]
    exact_mod_cast Fintype.card_pos
  refine ⟨scaleForm (Real.sqrt (formMass (cosetWedge H T)))⁻¹ (cosetWedge H T),
    (cosetWedge_fermion hT hTa).normalize hp,?_⟩
  rw [formEnergy_scale,formEnergy_cosetWedge hT hd,hw,inv_pow,
    Real.sq_sqrt (le_of_lt (show (0:ℝ) < Fintype.card (Equiv.Perm (Fin n) ⧸ H) by
      exact_mod_cast Fintype.card_pos))]
  field_simp

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_BlockWedge
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma tensor_subgroupFermion {N M : ℕ} {ψ : FormVector N} {φ : FormVector M}
    (hψ : SobolevFermion ψ) (hφ : SobolevFermion φ) :
    SubgroupFermion (blockSubgroup N M) (tensorForm ψ φ) := by
  intro κ hκ s
  obtain ⟨π,ρ,rfl⟩ := blockSubgroup_mem.mp hκ
  have hp : ∀ᵐ z : Configuration N × Configuration M,
      ψ.value (leftList s ∘ π) (z.1 ∘ π) =
        (((Equiv.Perm.sign π : ℤ) : ℂ) * ψ.value (leftList s) z.1) :=
    Measure.quasiMeasurePreserving_fst.ae (hψ.2.2.2 π (leftList s))
  have hq : ∀ᵐ z : Configuration N × Configuration M,
      φ.value (rightList s ∘ ρ) (z.2 ∘ ρ) =
        (((Equiv.Perm.sign ρ : ℤ) : ℂ) * φ.value (rightList s) z.2) :=
    Measure.quasiMeasurePreserving_snd.ae (hφ.2.2.2 ρ (rightList s))
  have ha := (configurationJoin_symm_preserving N M).quasiMeasurePreserving.ae hp
  have hb := (configurationJoin_symm_preserving N M).quasiMeasurePreserving.ae hq
  filter_upwards [ha,hb] with x hx hy
  simp only [configurationJoin_symm_apply] at hx hy
  change ψ.value _ _ * φ.value _ _ = _ * (ψ.value _ _ * φ.value _ _)
  rw [leftList_blockPerm,rightList_blockPerm,leftList_blockPerm,rightList_blockPerm,
    hx,hy,blockPerm_sign,Units.val_mul,Int.cast_mul]
  ring

theorem normalized_block_wedge_trial {N M : ℕ} {ψ : FormVector N} {φ : FormVector M}
    (hψ : FormAdmissible ψ) (hφ : FormAdmissible φ) (A : Set Space)
    (hc : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (he : ∀ x i, x i ∈ A → FormZeroAt φ x) (Z : ℝ) :
    ∃ F : FormVector (N+M), FormAdmissible F ∧ formEnergy Z F = formEnergy Z (tensorForm ψ φ) := by
  apply normalized_coset_wedge_trial
    (hψ.sobolevFermion.sobolevVector.tensor hφ.sobolevFermion.sobolevVector)
    (tensor_subgroupFermion hψ.sobolevFermion hφ.sobolevFermion)
  · rw [formMass_tensor,formMass,formMass,hψ.2.2.2.2.1,hφ.2.2.2.2.1,one_mul]
  · apply block_coset_terms_disjoint A
    · intro x i hx
      exact tensor_zero_left ψ φ (hc (leftList x) i hx)
    · intro x i hx
      exact tensor_zero_right ψ φ (he (rightList x) i hx)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_BlockEnergy
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma tensor_pair_right {N M : ℕ} (ψ : FormVector N) (φ : FormVector M)
    (s : Spins N) (t : Spins M) (i j : Fin M) :
    (∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 /
      ‖z (finSumFinEquiv (Sum.inr i))-z (finSumFinEquiv (Sum.inr j))‖) =
      (∫ x, ‖ψ.value s x‖^2)*(∫ y, ‖φ.value t y‖^2 / ‖y i-y j‖) := by
  change (∫ z, ‖ψ.value (leftList (joinLists s t)) (leftList z) *
    φ.value (rightList (joinLists s t)) (rightList z)‖^2 / ‖rightList z i-rightList z j‖) = _
  simp only [leftList_join,rightList_join,norm_mul,mul_pow,mul_div_assoc]
  exact integral_product_join (N := N) (M := M) (fun x => ‖ψ.value s x‖^2)
    (fun y => ‖φ.value t y‖^2 / ‖y i-y j‖)

lemma formRepulsion_tensor {N M : ℕ} (ψ : FormVector N) (φ : FormVector M) :
    formRepulsion (tensorForm ψ φ) = formRepulsion ψ * formMass φ +
      formMass ψ * formRepulsion φ + blockTensorCross ψ φ := by
  unfold formRepulsion blockTensorCross formMass
  rw [← sum_spin_join]
  have he (s : Spins N) (t : Spins M) :
      (∑ i : Fin (N+M), ∑ j : Fin (N+M), if i < j then
        ∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 / ‖z i-z j‖ else 0) =
      (∑ i : Fin N, ∑ j : Fin N, if i < j then ∫ x, ‖ψ.value s x‖^2 / ‖x i-x j‖ else 0)*
        (∫ y, ‖φ.value t y‖^2) +
      (∫ x, ‖ψ.value s x‖^2)*
        (∑ i : Fin M, ∑ j : Fin M, if i < j then ∫ y, ‖φ.value t y‖^2 / ‖y i-y j‖ else 0) +
      ∑ i : Fin N, ∑ j : Fin M,
        ∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 /
          ‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inr j))‖ := by
    rw [sum_pair_blocks]
    simp only [tensor_pair_left,tensor_pair_right,Finset.sum_mul,Finset.mul_sum,
      ite_mul,mul_ite,zero_mul,mul_zero]
  simp_rw [he,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum]
  congr 1
  exact Finset.sum_comm

lemma formEnergy_tensor {N M : ℕ} (ψ : FormVector N) (φ : FormVector M) (Z : ℝ) :
    formEnergy Z (tensorForm ψ φ) = formEnergy Z ψ * formMass φ +
      formMass ψ * formEnergy Z φ + blockTensorCross ψ φ := by
  rw [formEnergy_parts,formKinetic_tensor,formNuclear_tensor,formRepulsion_tensor,
    formEnergy_parts,formEnergy_parts]
  ring

theorem energy_le_block_insertion {N M : ℕ} {Z : ℝ} (hZ : 0 ≤ Z) {ψ : FormVector N} {φ : FormVector M}
    (hψ : FormAdmissible ψ) (hφ : FormAdmissible φ) (A : Set Space)
    (hc : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (he : ∀ x i, x i ∈ A → FormZeroAt φ x) :
    energy Z (N+M) ≤ formEnergy Z ψ + formEnergy Z φ + blockTensorCross ψ φ := by
  obtain ⟨F,hF,hE⟩ := normalized_block_wedge_trial hψ hφ A hc he Z
  have hv := energy_le_form hZ hF
  rw [hE,formEnergy_tensor,formMass,formMass,hψ.2.2.2.2.1,hφ.2.2.2.2.1,mul_one,one_mul] at hv
  exact hv

open MeasureTheory
open scoped BigOperators

lemma tensor_cross_pair_integrable {N M : ℕ} {ψ : FormVector N} {φ : FormVector M}
    (hψ : SobolevVector ψ) (hφ : SobolevVector φ)
    (s : Spins N) (t : Spins M) (i : Fin N) (j : Fin M) :
    Integrable (fun z : Configuration (N+M) =>
      ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 /
        ‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inr j))‖) := by
  apply (hψ.tensor hφ).pair_integrable
  exact fun h => Sum.inl_ne_inr (finSumFinEquiv.injective h)

lemma tensor_cross_pair_left_integrable {N M : ℕ} {ψ : FormVector N} {φ : FormVector M}
    (hψ : SobolevVector ψ) (hφ : SobolevVector φ)
    (s : Spins N) (t : Spins M) (i : Fin N) (j : Fin M) :
    Integrable (fun x : Configuration N => ‖ψ.value s x‖^2 *
      ∫ y : Configuration M, ‖φ.value t y‖^2 / ‖x i-y j‖) := by
  have hi := integrable_join (N := N) (M := M) (tensor_cross_pair_integrable hψ hφ s t i j)
  rw [Measure.volume_eq_prod] at hi
  have ht := hi.integral_prod_left
  simpa only [tensorForm_value_join,joinLists_left,joinLists_right,norm_mul,mul_pow,
    mul_div_assoc,integral_const_mul] using ht

lemma tensor_cross_pair {N M : ℕ} {ψ : FormVector N} {φ : FormVector M}
    (hψ : SobolevVector ψ) (hφ : SobolevVector φ)
    (s : Spins N) (t : Spins M) (i : Fin N) (j : Fin M) :
    (∫ z : Configuration (N+M), ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 /
      ‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inr j))‖) =
      ∫ x : Configuration N, ‖ψ.value s x‖^2 *
        ∫ y : Configuration M, ‖φ.value t y‖^2 / ‖x i-y j‖ := by
  have hi := tensor_cross_pair_integrable hψ hφ s t i j
  have hj := integrable_join (N := N) (M := M) hi
  have he := (configurationJoin_preserving N M).integral_comp
    (configurationJoin N M).toHomeomorph.measurableEmbedding (fun z : Configuration (N+M) =>
      ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 /
        ‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inr j))‖)
  simp only [configurationJoin_apply_prod] at he
  rw [Measure.volume_eq_prod] at hj he
  rw [← he,integral_prod _ hj]
  simp only [tensorForm_value_join,joinLists_left,joinLists_right,norm_mul,mul_pow,
    mul_div_assoc,integral_const_mul]

lemma blockCross_inner_integrable {N M : ℕ} {ψ : FormVector N} {φ : FormVector M}
    (hψ : SobolevVector ψ) (hφ : SobolevVector φ) (s : Spins N) (i : Fin N) :
    Integrable (fun x : Configuration N => ‖ψ.value s x‖^2 *
      ∑ t : Spins M, ∑ j : Fin M, ∫ y : Configuration M, ‖φ.value t y‖^2 / ‖x i-y j‖) := by
  simp_rw [Finset.mul_sum]
  exact integrable_finsetSum _ (fun t _ => integrable_finsetSum _ (fun j _ =>
    tensor_cross_pair_left_integrable hψ hφ s t i j))

lemma blockTensorCross_fubini {N M : ℕ} {ψ : FormVector N} {φ : FormVector M}
    (hψ : SobolevVector ψ) (hφ : SobolevVector φ) :
    blockTensorCross ψ φ = ∑ s : Spins N, ∑ i : Fin N,
      ∫ x : Configuration N, ‖ψ.value s x‖^2 *
        ∑ t : Spins M, ∑ j : Fin M, ∫ y : Configuration M, ‖φ.value t y‖^2 / ‖x i-y j‖ := by
  unfold blockTensorCross
  simp_rw [tensor_cross_pair hψ hφ]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun t _ => integrable_finsetSum _ (fun j _ =>
    tensor_cross_pair_left_integrable hψ hφ s t i j))]
  apply Finset.sum_congr rfl
  intro t _
  rw [integral_finsetSum _ (fun j _ => tensor_cross_pair_left_integrable hψ hφ s t i j)]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpinSpaceIntegrable
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
section Work_SpinSpaceIntegrable_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff

lemma slater_coulomb_integrable {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (j k : Fin n) (hjk : j ≠ k) :
    Integrable (fun z : Fin n → SlaterParticle => ‖slater φ z‖^2 / ‖(z j).2-(z k).2‖)
      (Measure.pi fun _ : Fin n => slaterParticleMeasure) := by
  apply spinSpace_integrable
  · exact ((continuous_slater (fun i => continuous_prod_of_discrete_left.mpr
      (fun s => (hφ i s).continuous))).measurable.norm.pow_const 2).div
      (((measurable_pi_apply j).snd.sub (measurable_pi_apply k).snd).norm)
  · intro s
    exact (slaterForm_sobolevFermion hφ hc).sobolevVector.pair_integrable s j k hjk

lemma slater_nuclear_integrable {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (j : Fin n) :
    Integrable (fun z : Fin n → SlaterParticle => ‖slater φ z‖^2 / ‖(z j).2‖)
      (Measure.pi fun _ : Fin n => slaterParticleMeasure) := by
  apply spinSpace_integrable
  · exact ((continuous_slater (fun i => continuous_prod_of_discrete_left.mpr
      (fun s => (hφ i s).continuous))).measurable.norm.pow_const 2).div
      (measurable_pi_apply j).snd.norm
  · intro s
    exact (slaterForm_sobolevFermion hφ hc).sobolevVector.nuclear_integrable s j

end Work_SpinSpaceIntegrable_scope

open MeasureTheory
open scoped BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterRepulsion
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
open scoped BigOperators ComplexConjugate ContDiff

lemma slater_repulsion_spinSpace {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x))) :
    formRepulsion (slaterForm φ) = (1/2:ℝ) * ∑ j : Fin n, ∑ k : Fin n,
      if j ≠ k then ∫ z, ‖slater φ z‖^2 / ‖(z j).2-(z k).2‖
        ∂Measure.pi (fun _ : Fin n => slaterParticleMeasure) else 0 := by
  rw [formRepulsion_ordered]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hjk : j ≠ k
  · simp only [ite_eq_left hjk]
    exact (spinSpace_integral _ (slater_coulomb_integrable hφ hc j k hjk)).symm
  · simp only [ite_eq_right hjk,Finset.sum_const_zero]

theorem slaterForm_repulsion {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z) * φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0) :
    formRepulsion (slaterForm φ) = (1/2:ℝ) * ∫ z : SlaterParticle × SlaterParticle,
      (slaterDirectDensity φ z.1 * slaterDirectDensity φ z.2 - slaterExchangeDensity φ z) /
        ‖z.1.2-z.2.2‖ ∂slaterParticleMeasure.prod slaterParticleMeasure := by
  have hl (i : Fin n) := memLp_spinSpace (fun s => (hφ i s).continuous) (hc i)
  have hi (j k : Fin n) (hjk : j ≠ k) :
      Integrable (fun z : Fin n → SlaterParticle => ‖(z j).2-(z k).2‖⁻¹ * ‖slater φ z‖^2)
        (Measure.pi fun _ : Fin n => slaterParticleMeasure) := by
    simpa only [div_eq_mul_inv,mul_comm] using slater_coulomb_integrable hφ hc j k hjk
  have ht := slater_two_body hl ho (fun z : SlaterParticle × SlaterParticle => ‖z.1.2-z.2.2‖⁻¹) hi
  rw [slater_repulsion_spinSpace hφ hc]
  simpa only [div_eq_mul_inv,mul_comm] using congrArg (fun x : ℝ => (1/2:ℝ)*x) ht

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff

lemma slaterForm_nuclear {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0) :
    formNuclear (slaterForm φ) = ∑ i : Fin n, ∫ z : SlaterParticle,
      ‖φ i z‖^2 / ‖z.2‖ ∂slaterParticleMeasure := by
  have hl (i : Fin n) := memLp_spinSpace (fun s => (hφ i s).continuous) (hc i)
  have hi (i : Fin n) : Integrable (fun z => ‖z.2‖⁻¹*‖φ i z‖^2) slaterParticleMeasure := by
    simpa only [div_eq_mul_inv,mul_comm] using orbital_nuclear_integrable (hφ i) (hc i)
  have hv (i : Fin n) := memLp_potential_mul
    (continuous_prod_of_discrete_left.mpr (fun s => (hφ i s).continuous)).measurable
    measurable_snd.norm.inv (fun z : SlaterParticle => inv_nonneg.mpr (norm_nonneg z.2)) (hi i)
  have ht := slater_nonnegative_potential hl ho (fun z : SlaterParticle => ‖z.2‖⁻¹)
    (fun z => inv_nonneg.mpr (norm_nonneg z.2)) hv
  have his (j : Fin n) := slater_nuclear_integrable hφ hc j
  have hs : (∫ z : Fin n → SlaterParticle, (∑ j, ‖(z j).2‖⁻¹)*‖slater φ z‖^2
      ∂Measure.pi (fun _ : Fin n => slaterParticleMeasure)) = formNuclear (slaterForm φ) := by
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum _ (fun j _ => by
      simpa only [div_eq_mul_inv,mul_comm] using his j)]
    unfold formNuclear
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = ∫ z : Fin n → SlaterParticle, ‖slater φ z‖^2 / ‖(z j).2‖
          ∂Measure.pi (fun _ : Fin n => slaterParticleMeasure) := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [div_eq_mul_inv,mul_comm]
      _ = _ := spinSpace_integral _ (his j)
  rw [hs] at ht
  simpa only [div_eq_mul_inv,mul_comm] using ht

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterOccupation
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
open scoped BigOperators ComplexConjugate ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

lemma core_orbital_integrable {N n : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    (s : Spins N) (j : Fin N) (i : Fin n) :
    Integrable (fun x : Configuration N => ‖ψ.value s x‖^2 * orbitalPole (φ i) (x j)) := by
  have hi := blockCross_inner_integrable hψ (slaterForm_sobolevFermion hφ hc).sobolevVector s j
  simp_rw [slaterForm_pole_trace hφ hc ho] at hi
  change Integrable (fun x : Configuration N => ‖ψ.value s x‖^2 * ∑ k : Fin n, orbitalPole (φ k) (x j)) at hi
  apply hi.mono' (((hψ.1 s).aestronglyMeasurable.norm.pow 2).mul
    ((orbitalPole_continuous (hφ i) (hc i)).comp (continuous_apply j)).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖‖ψ.value s x‖^2 * orbitalPole (φ i) (x j)‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (orbitalPole_nonneg _ _))]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun k _ => orbitalPole_nonneg (φ k) (x j))
    (Finset.mem_univ i)) (sq_nonneg _)

lemma blockTensorCross_slater {N n : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0) :
    blockTensorCross ψ (slaterForm φ) = ∑ k : Fin n, orbitalCoreInteraction ψ (φ k) := by
  rw [blockTensorCross_fubini hψ (slaterForm_sobolevFermion hφ hc).sobolevVector]
  simp_rw [slaterForm_pole_trace hφ hc ho]
  change (∑ s : Spins N, ∑ j : Fin N, ∫ x : Configuration N,
    ‖ψ.value s x‖^2 * ∑ k : Fin n, orbitalPole (φ k) (x j)) = _
  have he (s : Spins N) (j : Fin N) :
      (∫ x : Configuration N, ‖ψ.value s x‖^2 * ∑ k : Fin n, orbitalPole (φ k) (x j)) =
      ∑ k : Fin n, ∫ x : Configuration N, ‖ψ.value s x‖^2 * orbitalPole (φ k) (x j) := by
    simp_rw [Finset.mul_sum]
    exact integral_finsetSum _ (fun k _ => core_orbital_integrable hψ hφ hc ho s j k)
  simp_rw [he]
  calc
    _ = ∑ s : Spins N, ∑ k : Fin n, ∑ j : Fin N, ∫ x : Configuration N,
        ‖ψ.value s x‖^2 * orbitalPole (φ k) (x j) := by
      apply Finset.sum_congr rfl
      intro s _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma occupationSlater_cross {N n : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    (p : Fin n → ℝ) :
    (∑ m : Fin n → Bool, occupationWeight p m * blockTensorCross ψ (slaterForm (occupationOrbitals φ m))) =
      ∑ i : Fin n, p i * orbitalCoreInteraction ψ (φ i) := by
  have he (m : Fin n → Bool) : blockTensorCross ψ (slaterForm (occupationOrbitals φ m)) =
      ∑ i : Fin n, if m i then orbitalCoreInteraction ψ (φ i) else 0 := by
    rw [blockTensorCross_slater hψ (occupationOrbitals_smooth hφ m) (occupationOrbitals_compact hc m)
      (occupationOrbitals_orthonormal ho m)]
    exact occupationIndex_sum m (fun i => orbitalCoreInteraction ψ (φ i))
  simp_rw [he,occupation_sum]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_OccupationPairDensity
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
open scoped BigOperators ComplexConjugate ContDiff

lemma slaterPair_coulomb_integrable {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0) :
    Integrable (fun z : SlaterParticle × SlaterParticle =>
      slaterPairDensity φ z.1 z.2 / ‖z.1.2-z.2.2‖)
      (slaterParticleMeasure.prod slaterParticleMeasure) := by
  have hl (i : Fin n) := memLp_spinSpace (fun s => (hφ i s).continuous) (hc i)
  have he (z : SlaterParticle × SlaterParticle) :
      slaterPairDensity φ z.1 z.2 / ‖z.1.2-z.2.2‖ =
      ∑ j : Fin n, ∑ k : Fin n, ‖z.1.2-z.2.2‖⁻¹ *
        slaterPairMarginal (μ := slaterParticleMeasure) φ j k z := by
    simp_rw [← Finset.mul_sum]
    rw [slaterPairMarginal_sum hl ho]
    exact div_eq_inv_mul _ _
  simp_rw [he]
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro k _
  by_cases hjk : j ≠ k
  · apply slaterPairMarginal_observable_integrable hjk
    simpa only [div_eq_mul_inv,mul_comm] using slater_coulomb_integrable hφ hc j k hjk
  · simp only [slaterPairMarginal,ite_eq_right hjk,mul_zero]
    exact integrable_zero _ _ _

lemma occupationSlater_repulsion {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    (p : Fin n → ℝ) :
    (∑ m : Fin n → Bool, occupationWeight p m *
      formRepulsion (slaterForm (occupationOrbitals φ m))) =
      (1/2:ℝ) * ∫ z : SlaterParticle × SlaterParticle,
        (weightedSlaterDensity p φ z.1 * weightedSlaterDensity p φ z.2 -
          weightedSlaterExchange p φ z.1 z.2) / ‖z.1.2-z.2.2‖
          ∂slaterParticleMeasure.prod slaterParticleMeasure := by
  have hi (m : Fin n → Bool) := slaterPair_coulomb_integrable
    (occupationOrbitals_smooth hφ m) (occupationOrbitals_compact hc m)
    (occupationOrbitals_orthonormal ho m)
  have ht (m : Fin n → Bool) := slaterForm_repulsion
    (occupationOrbitals_smooth hφ m) (occupationOrbitals_compact hc m)
    (occupationOrbitals_orthonormal ho m)
  simp_rw [ht]
  calc
    _ = (1/2:ℝ) * ∑ m : Fin n → Bool, ∫ z : SlaterParticle × SlaterParticle,
        occupationWeight p m * (slaterPairDensity (occupationOrbitals φ m) z.1 z.2 /
          ‖z.1.2-z.2.2‖) ∂slaterParticleMeasure.prod slaterParticleMeasure := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [integral_const_mul]
      change occupationWeight p m * ((1/2:ℝ) *
        (∫ z : SlaterParticle × SlaterParticle, slaterPairDensity (occupationOrbitals φ m) z.1 z.2 /
          ‖z.1.2-z.2.2‖ ∂slaterParticleMeasure.prod slaterParticleMeasure)) = _
      ring
    _ = (1/2:ℝ) * ∫ z : SlaterParticle × SlaterParticle,
        ∑ m : Fin n → Bool, occupationWeight p m *
          (slaterPairDensity (occupationOrbitals φ m) z.1 z.2 / ‖z.1.2-z.2.2‖)
          ∂slaterParticleMeasure.prod slaterParticleMeasure := by
      rw [integral_finsetSum _ (fun m _ => (hi m).const_mul _)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [← mul_div_assoc,← Finset.sum_div,occupationPairDensity]

lemma occupationSlater_repulsion_le_direct {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    (p : Fin n → ℝ) :
    (∑ m : Fin n → Bool, occupationWeight p m *
      formRepulsion (slaterForm (occupationOrbitals φ m))) ≤
      (1/2:ℝ) * ∫ z : SlaterParticle × SlaterParticle,
        (weightedSlaterDensity p φ z.1 * weightedSlaterDensity p φ z.2) / ‖z.1.2-z.2.2‖
          ∂slaterParticleMeasure.prod slaterParticleMeasure := by
  rw [occupationSlater_repulsion hφ hc ho p]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hi : Integrable (fun z : SlaterParticle × SlaterParticle =>
      (weightedSlaterDensity p φ z.1 * weightedSlaterDensity p φ z.2 -
        weightedSlaterExchange p φ z.1 z.2) / ‖z.1.2-z.2.2‖)
        (slaterParticleMeasure.prod slaterParticleMeasure) := by
    have he (z : SlaterParticle × SlaterParticle) :
        (weightedSlaterDensity p φ z.1 * weightedSlaterDensity p φ z.2 -
          weightedSlaterExchange p φ z.1 z.2) / ‖z.1.2-z.2.2‖ =
        ∑ m : Fin n → Bool, occupationWeight p m *
          (slaterPairDensity (occupationOrbitals φ m) z.1 z.2 / ‖z.1.2-z.2.2‖) := by
      simp only [← mul_div_assoc,← Finset.sum_div,occupationPairDensity]
    simp_rw [he]
    exact integrable_finsetSum _ (fun m _ => (slaterPair_coulomb_integrable
      (occupationOrbitals_smooth hφ m) (occupationOrbitals_compact hc m)
      (occupationOrbitals_orthonormal ho m)).const_mul _)
  apply integral_mono hi (weightedSlater_direct_coulomb_integrable hφ hc p)
  intro z
  exact div_le_div_of_nonneg_right (sub_le_self _ (sq_nonneg _)) (norm_nonneg _)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_OccupationTraces
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

namespace CoulombAtom

lemma occupationSlater_nuclear {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    (p : Fin n → ℝ) :
    (∑ m : Fin n → Bool, occupationWeight p m * formNuclear (slaterForm (occupationOrbitals φ m))) =
      ∑ i : Fin n, p i * ∫ z : SlaterParticle, ‖φ i z‖^2 / ‖z.2‖ ∂slaterParticleMeasure := by
  have he (m : Fin n → Bool) : formNuclear (slaterForm (occupationOrbitals φ m)) =
      ∑ i : Fin n, if m i then (∫ z : SlaterParticle, ‖φ i z‖^2 / ‖z.2‖ ∂slaterParticleMeasure) else 0 := by
    rw [slaterForm_nuclear (occupationOrbitals_smooth hφ m) (occupationOrbitals_compact hc m)
      (occupationOrbitals_orthonormal ho m)]
    exact occupationIndex_sum m (fun i => ∫ z : SlaterParticle, ‖φ i z‖^2 / ‖z.2‖ ∂slaterParticleMeasure)
  simp_rw [he,occupation_sum]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_FiniteFermionEnsemble
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

namespace CoulombAtom

lemma occupationSlater_energy_le {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    (Z lam : ℝ) (p : Fin n → ℝ) :
    (∑ m : Fin n → Bool, occupationWeight p m *
      (formEnergy Z (slaterForm (occupationOrbitals φ m)) + lam * Fintype.card (Occupied m))) ≤
      finiteOccupationEnergy Z lam p φ := by
  simp only [formEnergy_parts,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp_rw [mul_left_comm (occupationWeight p _) Z,mul_left_comm (occupationWeight p _) lam]
  rw [← Finset.mul_sum,← Finset.mul_sum,occupationSlater_kinetic hφ hc ho,
    occupationSlater_nuclear hφ hc ho,occupation_count]
  have ht := occupationSlater_repulsion_le_direct hφ hc ho p
  dsimp only [finiteOccupationEnergy]
  linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CorrelatedFiniteInsertion
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
open scoped BigOperators ComplexConjugate ContDiff

theorem price_le_correlated_finite_insertion {N n : ℕ} {ψ : FormVector N}
    (hψ : FormAdmissible ψ) {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (hsep : ∀ i s, Disjoint A (tsupport (fun y : Space => φ i (s,y))))
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    priceEnergy (energy Z) lam ≤ formEnergy Z ψ + lam * N +
      finiteOccupationEnergy Z lam p φ + ∑ i : Fin n, p i * orbitalCoreInteraction ψ (φ i) := by
  have he (m : Fin n → Bool) : priceEnergy (energy Z) lam ≤
      (formEnergy Z ψ + lam*N) +
      (formEnergy Z (slaterForm (occupationOrbitals φ m)) + lam * Fintype.card (Occupied m)) +
      blockTensorCross ψ (slaterForm (occupationOrbitals φ m)) := by
    have ha := occupationSlater_admissible hφ hc ho m
    have hb := energy_le_block_insertion hZ hψ ha A hcore (occupationSlater_outside φ A hsep m)
    have ht := quantum_price_le_sector hZ hlam (N + Fintype.card (Occupied m))
    push_cast at ht
    linarith
  have hm := occupation_mean_lower hp _ he
  simp only [mul_add,Finset.sum_add_distrib] at hm
  rw [← Finset.sum_mul,occupationWeight_sum,one_mul,
    occupationSlater_cross hψ.sobolevFermion.sobolevVector hφ hc ho] at hm
  simp only [← Finset.sum_mul,occupationWeight_sum,one_mul] at hm
  have hb := occupationSlater_energy_le hφ hc ho Z lam p
  simp only [mul_add,Finset.sum_add_distrib] at hb
  linarith

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

universe u

theorem price_le_correlated_fintype_insertion {ι : Type u} [Fintype ι] [DecidableEq ι]
    {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ) {φ : ι → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (hsep : ∀ i s, Disjoint A (tsupport (fun y : Space => φ i (s,y))))
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    priceEnergy (energy Z) lam ≤ formEnergy Z ψ + lam * N +
      finiteOrbitalEnergy Z lam p φ + ∑ i, p i * orbitalCoreInteraction ψ (φ i) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have ho' (i j) : (∫ z, conj ((φ ∘ e) i z)*(φ ∘ e) j z ∂slaterParticleMeasure) =
      if i=j then 1 else 0 := by
    simp only [Function.comp_apply, ho, Equiv.apply_eq_iff_eq]
  have h := price_le_correlated_finite_insertion hψ (fun i s => hφ (e i) s)
    (fun i s => hc (e i) s) ho' A hcore (fun i s => hsep (e i) s) hZ hlam (fun i => hp (e i))
  change priceEnergy (energy Z) lam ≤ formEnergy Z ψ + lam * N +
    finiteOccupationEnergy Z lam (p ∘ e) (φ ∘ e) +
      ∑ i, p (e i) * orbitalCoreInteraction ψ (φ (e i)) at h
  rw [finiteOrbitalEnergy_reindex e Z lam p φ] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  exact (e.sum_comp (fun i => p i * orbitalCoreInteraction ψ (φ i))).symm

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ArraySymmetry
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

def quantumEventProbability {N : ℕ} {J : Type*} [Fintype J]
    (F : fermionGraph N) (b : J → ℝ) (s : Set (J × (Fin N × Fin 3) → ℝ)) : ℝ :=
  ∫ x, quantumEventLikelihood b s x ∂graphRawLaw F

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_BlockSwap
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma swapBlocks_sobolev {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ) :
    SobolevVector (swapBlocks ψ) := hψ.reindex _

lemma swapBlocks_coreKinetic {N M : ℕ} (ψ : FormVector (N+M)) :
    coreKinetic (swapBlocks ψ) = outKinetic ψ := by
  have hi (s : Spins (M+N)) (i : Fin M) (a : Fin 3) :
      (∫ x, ‖(swapBlocks ψ).gradient s (finSumFinEquiv (Sum.inl i)) a x‖^2) =
      ∫ x, ‖ψ.gradient (s ∘ (blockSwap N M).symm) (finSumFinEquiv (Sum.inr i)) a x‖^2 := by
    simpa only [swapBlocks,reindexForm,blockSwap_left] using
      integral_reindex (blockSwap N M) (fun x =>
        ‖ψ.gradient (s ∘ (blockSwap N M).symm) (finSumFinEquiv (Sum.inr i)) a x‖^2)
  unfold coreKinetic
  simp_rw [hi]
  exact congrArg (fun z : ℝ => (1/2:ℝ)*z)
    (sum_spin_reindex (blockSwap N M) (fun s => ∑ i : Fin M, ∑ a,
      ∫ x, ‖ψ.gradient s (finSumFinEquiv (Sum.inr i)) a x‖^2))

lemma swapBlocks_coreRepulsion {N M : ℕ} (ψ : FormVector (N+M)) :
    coreRepulsion (swapBlocks ψ) = outRepulsion ψ := by
  unfold coreRepulsion swapBlocks
  have he (s : Spins (M+N)) (i j : Fin M) :
      (∫ x : Configuration (M+N),
        ‖(reindexForm (blockSwap N M) ψ).value s x‖^2 /
          ‖x (finSumFinEquiv (Sum.inl i))-x (finSumFinEquiv (Sum.inl j))‖) =
      ∫ x : Configuration (N+M), ‖ψ.value (s ∘ (blockSwap N M).symm) x‖^2 /
        ‖x (finSumFinEquiv (Sum.inr i))-x (finSumFinEquiv (Sum.inr j))‖ := by
    convert integral_reindex (blockSwap N M) (fun x =>
      ‖ψ.value (s ∘ (blockSwap N M).symm) x‖^2 /
        ‖x (finSumFinEquiv (Sum.inr i))-x (finSumFinEquiv (Sum.inr j))‖) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [reindexForm,Function.comp_apply,←blockSwap_left N M,
      Equiv.symm_apply_apply]
  simp_rw [he]
  exact sum_spin_reindex (blockSwap N M) (fun s => ∑ i : Fin M, ∑ j : Fin M,
    if i < j then ∫ x, ‖ψ.value s x‖^2 /
      ‖x (finSumFinEquiv (Sum.inr i))-x (finSumFinEquiv (Sum.inr j))‖ else 0)

open MeasureTheory Filter Set
open scoped BigOperators

open CoulombNeumann

lemma weighted_coreSlice_reorder {N M : ℕ} (ψ : FormVector (N+M))
    (F : Spins M → Configuration M → ℝ)
    (hF : ∀ s : Spins M, ∀ t : Spins N,
      Integrable (fun p : Configuration M × Configuration N =>
        F s p.1*‖(swapBlocks ψ).value (joinLists s t) (joinLists p.1 p.2)‖^2)) :
    (∑ t : Spins N, ∫ y : Configuration N, ∑ s : Spins M, ∫ x : Configuration M,
      F s x*‖(coreSlice (swapBlocks ψ) t y).value s x‖^2) =
      ∑ s : Spins M, ∫ x : Configuration M, F s x*formMass (coreSlice ψ s x) := by
  have he (s : Spins M) (t : Spins N) :
      (∫ y : Configuration N, ∫ x : Configuration M,
        F s x*‖(coreSlice (swapBlocks ψ) t y).value s x‖^2) =
      ∫ x : Configuration M, F s x*(∫ y : Configuration N,
        ‖(coreSlice ψ s x).value t y‖^2) := by
    change (∫ y : Configuration N, ∫ x : Configuration M,
      F s x*‖(swapBlocks ψ).value (joinLists s t) (joinLists x y)‖^2) = _
    rw [←integral_prod_symm _ (hF s t),integral_prod _ (hF s t)]
    simp only [coreSlice,swapBlocks_value,integral_const_mul]
  have hs (t : Spins N) : (∫ y : Configuration N, ∑ s : Spins M, ∫ x : Configuration M,
      F s x*‖(coreSlice (swapBlocks ψ) t y).value s x‖^2) =
      ∑ s : Spins M, ∫ y : Configuration N, ∫ x : Configuration M,
        F s x*‖(coreSlice (swapBlocks ψ) t y).value s x‖^2 :=
    integral_finsetSum _ (fun s _ => (hF s t).integral_prod_right)
  simp_rw [hs,he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hi (t : Spins N) : Integrable (fun x : Configuration M =>
      F s x*(∫ y : Configuration N, ‖(coreSlice ψ s x).value t y‖^2)) := by
    have hh := (hF s t).integral_prod_left
    simpa only [swapBlocks_value,coreSlice,integral_const_mul] using hh
  rw [←integral_finsetSum _ (fun t _ => hi t)]
  simp only [formMass,Finset.mul_sum]

lemma retained_pressure_join_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) {b : ℝ} (hb : 0 < b)
    (S : Configuration N × Configuration M → Finset (Fin N))
    (hS : ∀ i, MeasurableSet {p | i ∈ S p}) (s : Spins N) (t : Spins M) :
    Integrable (fun p : Configuration N × Configuration M =>
      retainedPressure b (S p) p.1*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2) := by
  have hi := integrable_join (N := N) (M := M) (hψ.1 (joinLists s t)).norm.integrable_sq
  have hm := retainedPressure_measurable_param b S Prod.fst hS measurable_fst
  apply hi.bdd_mul hm.aestronglyMeasurable
  exact Eventually.of_forall (fun p => by
    change ‖retainedPressure b (S p) p.1‖ ≤ b⁻¹^2*(N:ℝ)^(5/3:ℝ)
    rw [Real.norm_of_nonneg (retainedPressure_nonneg hb _ _)]
    exact (retainedPressure_le_average hb _ _).trans (physicalPressureAverage_le b p.1))

lemma retained_direct_join_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) {b : ℝ} (hb : 0 < b)
    (S : Configuration N × Configuration M → Finset (Fin N))
    (hS : ∀ i, MeasurableSet {p | i ∈ S p}) (s : Spins N) (t : Spins M) :
    Integrable (fun p : Configuration N × Configuration M =>
      retainedDirect b (S p) p.1*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2) := by
  have hi := integrable_join (N := N) (M := M) (hψ.1 (joinLists s t)).norm.integrable_sq
  have hm := retainedDirect_measurable_param b S Prod.fst hS measurable_fst
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
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hh := retained_physical_coulomb_lower hb (S p) p.1 hp
  change retainedDirect b (S p) p.1-_ ≤ pointRepulsion p.1 at hh
  linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_ConditionalObservables
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
open CoulombNeumann

lemma weighted_coreSlice_integrable {N M : ℕ} (ψ : FormVector (N+M)) (s : Spins M)
    (F : Configuration M → ℝ)
    (hF : ∀ t : Spins N, Integrable (fun p : Configuration M × Configuration N =>
      F p.1*‖(swapBlocks ψ).value (joinLists s t) (joinLists p.1 p.2)‖^2)) :
    Integrable (fun x => F x*formMass (coreSlice ψ s x)) := by
  have hi (t : Spins N) : Integrable (fun x : Configuration M =>
      F x*(∫ y : Configuration N, ‖(coreSlice ψ s x).value t y‖^2)) := by
    simpa only [swapBlocks_value,coreSlice,integral_const_mul] using (hF t).integral_prod_left
  simpa only [formMass,Finset.mul_sum] using integrable_finsetSum Finset.univ (fun t _ => hi t)

lemma retained_pressure_weighted_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) {b : ℝ} (hb : 0 < b) (s : Spins M)
    (S : Configuration M → Finset (Fin M)) (hS : ∀ i, MeasurableSet {x | i ∈ S x}) :
    Integrable (fun x => retainedPressure b (S x) x*formMass (coreSlice ψ s x)) :=
  weighted_coreSlice_integrable ψ s _ (fun t => retained_pressure_join_integrable
    (swapBlocks_sobolev hψ) hb (fun p => S p.1) (fun i => measurable_fst (hS i)) s t)

lemma retained_direct_weighted_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) {b : ℝ} (hb : 0 < b) (s : Spins M)
    (S : Configuration M → Finset (Fin M)) (hS : ∀ i, MeasurableSet {x | i ∈ S x}) :
    Integrable (fun x => retainedDirect b (S x) x*formMass (coreSlice ψ s x)) :=
  weighted_coreSlice_integrable ψ s _ (fun t => retained_direct_join_integrable
    (swapBlocks_sobolev hψ) hb (fun p => S p.1) (fun i => measurable_fst (hS i)) s t)

def conditionalRetainedFieldSum {N M : ℕ} (Z lam : ℝ) (ψ : FormVector (N+M))
    (s : Spins M) (S : Configuration M → Finset (Fin M)) (x : Configuration M) : ℝ :=
  formMass (coreSlice ψ s x)*∑ i ∈ S x, normalizedCoreField Z lam (coreSlice ψ s x) (x i)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_CoreFieldRegularity
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

attribute [local instance] OAI.CoulombAtom.instFactNeENNRealHDivOfNatTop_solutions
attribute [local instance] OAI.CoulombAtom.instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFField
local instance instBorelSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFField_r394ffd_1 (R : ℝ) : BorelSpace (TFField R) := ⟨rfl⟩
attribute [local instance] OAI.CoulombAtom.instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp
local instance instBorelSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_r394ffd_1 (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩
lemma conditionalPatchField_aemeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) (y : Space) (R : ℝ) :
    AEMeasurable (conditionalPatchField ψ t Z lam y R) := by
  obtain ⟨F,hF,he⟩ := coreSlice_field_measurable_rep hψ t Z lam
  have hm : Measurable (fun q : Configuration M × Space => F (q.1,y+q.2)) :=
    hF.comp (measurable_fst.prodMk (measurable_const.add measurable_snd))
  have hh := measurable_toLpOrZero (μ := ballMeasure R) (p := 5/2)
    (f := fun u z => F (u,y+z)) hm
  apply hh.aemeasurable.congr
  filter_upwards [he] with u hu
  apply toLpOrZero_congr (f := fun u z => F (u,y+z))
    (g := fun u z => normalizedCoreField Z lam (coreSlice ψ t u) (y+z))
  exact ae_of_all _ (fun z => hu (y+z))

lemma conditionalPatchMinimizer_aemeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) (y : Space) (R : ℝ) :
    AEMeasurable (fun u => tfPatchMinimizer R tfKinetic tfKinetic_pos
      (conditionalPatchField ψ t Z lam y R u)) :=
  (tfPatchMinimizer_measurable R tfKinetic tfKinetic_pos).comp_aemeasurable
    (conditionalPatchField_aemeasurable hψ t Z lam y R)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_CoherentFiniteInsertion
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff

namespace CoulombAtom

theorem price_le_coherent_finite_insertion {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ)
    {g : Space → ℂ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x : Space, ‖g x‖^2 = 1)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (hμle : μ ≤ volume)
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (hsep : Disjoint A (coherentSpatialSupport g K))
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    (s : Finset (CoherentPositiveIndex hg.continuous hcg μ)) :
    priceEnergy (energy Z) lam ≤ formEnergy Z ψ + lam * N +
      finiteOrbitalEnergy Z lam
        (fun i : Fin 2 × s => coherentWeight hg.continuous hcg μ i.2.1.1)
        (fun i => spinLift (coherentOrbital hg.continuous hcg μ i.2.1.1) i.1) +
      ∑ i : Fin 2 × s, coherentWeight hg.continuous hcg μ i.2.1.1 *
        orbitalCoreInteraction ψ (spinLift (coherentOrbital hg.continuous hcg μ i.2.1.1) i.1) := by
  classical
  apply price_le_correlated_fintype_insertion hψ
  · intro i σ
    exact spinLift_smooth (coherentOrbital_smooth hg hcg μ hK hμ i.2.1.1) i.1 σ
  · intro i σ
    exact spinLift_compact (coherentOrbital_compact hg.continuous hcg μ hK hμ i.2.1.1) i.1 σ
  · apply spinFinite_orthonormal (u := fun i : s => coherentOrbital hg.continuous hcg μ i.1.1)
    intro i j
    rw [coherentOrbital_inner hg hcg μ hK hμ i.1.1 j.1.1 i.1.2.ne' j.1.2.ne']
    simp only [(orthonormal_iff_ite.mp (coherentBasis hg.continuous hcg μ).orthonormal),
      Subtype.ext_iff]
  · exact hcore
  · intro i σ
    exact spinLift_separated (hsep.mono_right
      (coherentOrbital_tsupport_subset hg.continuous hcg μ hK hμ i.2.1.1)) i.1 σ
  · exact hZ
  · exact hlam
  · intro i
    exact ⟨i.2.1.2.le,coherentWeight_le_one hg hcg hgn μ hμle i.2.1.1⟩

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoherentLimitInsertion
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ContDiff Topology

namespace CoulombAtom

theorem price_le_coherent_insertion {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ)
    {g : Space → ℂ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x : Space, ‖g x‖^2 = 1)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (hμle : μ ≤ volume)
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (hsep : Disjoint A (coherentSpatialSupport g K))
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    priceEnergy (energy Z) lam ≤ formEnergy Z ψ + lam * N + coherentSpinKinetic g μ +
      2 * (∫ r : Space × Space, coherentDensity g μ r.1 * coherentDensity g μ r.2 / ‖r.1-r.2‖) -
      2*Z*CoulombAnalysis.tfPotential (coherentDensity g μ) 0 +
      2*lam*(∫ x : Space, coherentDensity g μ x) +
      2*coreDensityInteraction ψ (coherentDensity g μ) := by
  classical
  let b (i : CoherentPositiveIndex hg.continuous hcg μ) : ℝ :=
    -(2*Z) * (coherentWeight hg.continuous hcg μ i.1 *
      CoulombAnalysis.tfPotential (fun y => ‖coherentOrbital hg.continuous hcg μ i.1 y‖^2) 0) +
    (2*lam) * coherentWeight hg.continuous hcg μ i.1 +
    2 * (coherentWeight hg.continuous hcg μ i.1 * coreDensityInteraction ψ
      (fun y => ‖coherentOrbital hg.continuous hcg μ i.1 y‖^2))
  have hm : HasSum (fun i : CoherentPositiveIndex hg.continuous hcg μ =>
      coherentWeight hg.continuous hcg μ i.1) (∫ x : Space, coherentDensity g μ x) := by
    rw [coherentDensity_mass hg.continuous hcg μ hK hμ]
    exact coherentPositiveWeight_hasSum hg.continuous hcg μ
  have hs : HasSum b (-(2*Z)*CoulombAnalysis.tfPotential (coherentDensity g μ) 0 +
      (2*lam)*(∫ x : Space, coherentDensity g μ x) + 2*coreDensityInteraction ψ (coherentDensity g μ)) :=
    (((coherentOrbital_pole_hasSum hg hcg μ hK hμ 0).mul_left (-(2*Z))).add
      (hm.mul_left (2*lam))).add ((coherentOrbital_core_hasSum hψ.sobolevFermion.sobolevVector hg hcg μ hK hμ).mul_left 2)
  have hb (s : Finset (CoherentPositiveIndex hg.continuous hcg μ)) :
      priceEnergy (energy Z) lam ≤ formEnergy Z ψ + lam * N + coherentSpinKinetic g μ +
        2 * (∫ r : Space × Space, coherentDensity g μ r.1 * coherentDensity g μ r.2 / ‖r.1-r.2‖) +
        ∑ i ∈ s, b i := by
    have hf := price_le_coherent_finite_insertion hψ hg hcg hgn μ hμle hK hμ A hcore hsep hZ hlam s
    rw [spinFinite_energy (fun i : s => coherentWeight hg.continuous hcg μ i.1.1)
      (u := fun i : s => coherentOrbital hg.continuous hcg μ i.1.1)
      (fun i => (coherentOrbital_smooth hg hcg μ hK hμ i.1.1).continuous) Z lam,
      spinFinite_core ψ (fun i : s => coherentWeight hg.continuous hcg μ i.1.1)
        (fun i : s => coherentOrbital hg.continuous hcg μ i.1.1)] at hf
    have hk := coherentFinite_kinetic_le hg hcg μ hK hμ s
    have hd := coherentFinite_direct_le hg hcg μ hK hμ s
    rw [← Finset.sum_coe_sort s b]
    simp only [b,Finset.sum_add_distrib,← Finset.mul_sum]
    linarith
  have hh := ge_of_tendsto (tendsto_const_nhds.add hs) (Eventually.of_forall hb)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CoherentRealKinetic
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
open scoped BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

theorem price_le_smeared_packet_insertion {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ)
    {ρ g : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x : Space, (g x)^2 = 1)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (hsep : Disjoint A (packetRegion g J))
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    priceEnergy (energy Z) lam ≤ formEnergy Z ψ + lam*N +
      tfKinetic*(∫ z, (ρ z)^(5/3 : ℝ)) + (packetDirichlet g/2)*(∫ z, ρ z) +
      (1/2:ℝ)*(∫ r : Space × Space, smearedPacketDensity g ρ r.1*smearedPacketDensity g ρ r.2/‖r.1-r.2‖) -
      Z*CoulombAnalysis.tfPotential (smearedPacketDensity g ρ) 0 +
      lam*(∫ z, ρ z) + coreDensityInteraction ψ (smearedPacketDensity g ρ) := by
  let := fermiMeasure_finite hn hJ hs hb
  have hgc : ContDiff ℝ ∞ (fun x : Space => (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have hcgc : HasCompactSupport (fun x : Space => (g x : ℂ)) :=
    hcg.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hgg : (∫ x : Space, ‖(g x : ℂ)‖^2) = 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,sq_abs] using hgn
  have hf := price_le_coherent_insertion hψ hgc hcgc hgg (fermiMeasure ρ)
    (fermiMeasure_le ρ) (hJ.prod (isCompact_closedBall _ _)) (fermiMeasure_mem hm hn hs hb)
    A hcore (hsep.mono_right (coherentSupport_fermi_subset g J _)) hZ hlam
  let d := coherentDensity (fun x => (g x : ℂ)) (fermiMeasure ρ)
  have he : smearedPacketDensity g ρ = fun x => 2*d x :=
    funext (fun x => (coherentDensity_fermi hm hn hJ hs hb hg.continuous x).symm)
  have hmass : ∫ z, ρ z = 2*(∫ x : Space, d x) := by
    rw [← smearedPacketDensity_mass hm hn hJ hs hb hg.continuous hcg hgn,he,integral_const_mul]
  rw [he,coulomb_double_const_mul,potential_const_mul,coreDensityInteraction_const_mul,hmass]
  rw [coherentSpinKinetic_fermi hm hn hJ hs hb hg hcg hgn] at hf
  rw [hmass] at hf
  dsimp only [d]
  linarith

theorem price_le_radial_packet_insertion {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ)
    {ρ g : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x : Space, (g x)^2 = 1) (hr : CoulombAnalysis.IsRadial (fun x => (g x)^2))
    {R : ℝ} (hR : 0 < R) (hgs : ∀ y, g y ≠ 0 → ‖y‖ ≤ R)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (hsep : Disjoint A (packetRegion g J))
    (hnuc : ∀ z ∈ J, R ≤ ‖z‖) (hcs : ∀ a ∈ A, ∀ z ∈ J, R ≤ ‖a-z‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    priceEnergy (energy Z) lam ≤ formEnergy Z ψ + lam*N +
      tfKinetic*(∫ z, (ρ z)^(5/3 : ℝ)) + (packetDirichlet g/2)*(∫ z, ρ z) +
      (1/2:ℝ)*(∫ r : Space × Space, ρ r.1*ρ r.2/‖r.1-r.2‖) -
      Z*CoulombAnalysis.tfPotential ρ 0 + lam*(∫ z, ρ z) + coreDensityInteraction ψ ρ := by
  have hab (z : Space) : |ρ z| ≤ B := by rw [abs_of_nonneg (hn z)]; exact hb z
  have h1 : Integrable ρ := bounded_compact_integrable hm hJ hs hab
  have hs2 (y : Space) (hy : (g y)^2 ≠ 0) : ‖y‖ ≤ R := hgs y (fun hz => hy (by simp [hz]))
  have hmean (a : Space) (ha : ∀ z, ρ z ≠ 0 → R ≤ ‖a-z‖) :
      CoulombAnalysis.tfPotential (smearedPacketDensity g ρ) a = CoulombAnalysis.tfPotential ρ a :=
    spatialSmearing_potential_eq (hg.continuous.pow 2) (square_compact hcg) hr hgn hm h1 hR hs2 a ha
  have hzero : CoulombAnalysis.tfPotential (smearedPacketDensity g ρ) 0 = CoulombAnalysis.tfPotential ρ 0 :=
    hmean 0 (fun z hz => by simpa only [zero_sub,norm_neg] using hnuc z (hs hz))
  have hcross : coreDensityInteraction ψ (smearedPacketDensity g ρ) = coreDensityInteraction ψ ρ := by
    unfold coreDensityInteraction
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases ha : x j ∈ A
    · rw [hmean (x j) (fun z hz => hcs (x j) ha z (hs hz))]
    · have hz := (hcore x j ha s).1
      simp only [hz,norm_zero,zero_pow (by norm_num : 2 ≠ 0),zero_mul]
  have hf := price_le_smeared_packet_insertion hψ hm hn hJ hs hb hg hcg hgn A hcore hsep hZ hlam
  rw [hzero,hcross] at hf
  have hd := smearedPacketDensity_direct_le hm hn hJ hs hb hg.continuous hcg hgn hr
  linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PacketScale
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
open scoped BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

theorem price_le_scaled_packet_insertion {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ)
    {ρ g : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x : Space, (g x)^2 = 1) (hr : CoulombAnalysis.IsRadial g)
    (hgs : tsupport g ⊆ ball 0 1) {b : ℝ} (hpositive : 0 < b)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (hsep : Disjoint A (packetRegion (scaledRealPacket b g) J))
    (hnuc : ∀ z ∈ J, b ≤ ‖z‖) (hcs : ∀ a ∈ A, ∀ z ∈ J, b ≤ ‖a-z‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    priceEnergy (energy Z) lam ≤ formEnergy Z ψ + lam*N +
      tfKinetic*(∫ z, (ρ z)^(5/3 : ℝ)) + (packetDirichlet g/2)*b⁻¹^2*(∫ z, ρ z) +
      (1/2:ℝ)*(∫ r : Space × Space, ρ r.1*ρ r.2/‖r.1-r.2‖) -
      Z*CoulombAnalysis.tfPotential ρ 0 + lam*(∫ z, ρ z) + coreDensityInteraction ψ ρ := by
  have hrad : CoulombAnalysis.IsRadial (fun x => (scaledRealPacket b g x)^2) := by
    intro x y hxy
    dsimp only
    rw [scaledRealPacket_radial b hr x y hxy]
  have hnorm : (∫ x : Space, (scaledRealPacket b g x)^2) = 1 := by
    rw [scaledRealPacket_mass hpositive,hgn]
  have hh := price_le_radial_packet_insertion hψ hm hn hJ hs hb
    (scaledRealPacket_smooth b hg) (scaledRealPacket_compact hpositive hcg)
    hnorm hrad hpositive (fun y hy => (scaledRealPacket_support hpositive hgs hy).le)
    A hcore hsep hnuc hcs hZ hlam
  rw [scaledRealPacket_dirichlet hpositive hg] at hh
  convert hh using 1 <;> first | rfl | ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_PricedUpperComparison
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

theorem priced_patch_upper_comparison {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ)
    {ρ g : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x : Space, (g x)^2 = 1) (hr : CoulombAnalysis.IsRadial g)
    (hgs : tsupport g ⊆ ball 0 1) {b : ℝ} (hpositive : 0 < b)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (hsep : Disjoint A (packetRegion (scaledRealPacket b g) J))
    (hnuc : ∀ z ∈ J, b ≤ ‖z‖) (hcs : ∀ a ∈ A, ∀ z ∈ J, b ≤ ‖a-z‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    priceEnergy (energy Z) lam ≤ formEnergy Z ψ + lam*N +
      tfKinetic*(∫ z, (ρ z)^(5/3 : ℝ)) + (packetDirichlet g/2)*b⁻¹^2*(∫ z, ρ z) -
      (∫ y : Space, (Z/‖y‖-lam-coreCoulombAt ψ y)*ρ y) +
      (1/2:ℝ)*(∫ r : Space × Space, ρ r.1*ρ r.2/‖r.1-r.2‖) := by
  have hab : ∀ z, |ρ z| ≤ B := fun z => by rw [abs_of_nonneg (hn z)]; exact hb z
  rw [priced_core_field_pairing hψ.sobolevFermion.sobolevVector hm hJ hs hab]
  have hh := price_le_scaled_packet_insertion hψ hm hn hJ hs hb hg hcg hgn hr hgs hpositive
    A hcore hsep hnuc hcs hZ hlam
  linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_ConditionalPricedUpper
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
open scoped BigOperators ContDiff

namespace CoulombAtom

theorem conditional_priced_patch_upper {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    {ρ g : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x : Space, (g x)^2 = 1) (hr : CoulombAnalysis.IsRadial g)
    (hgs : tsupport g ⊆ ball 0 1) {b : ℝ} (hpositive : 0 < b)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (hsep : Disjoint A (packetRegion (scaledRealPacket b g) J))
    (hnuc : ∀ z ∈ J, b ≤ ‖z‖) (hcs : ∀ a ∈ A, ∀ z ∈ J, b ≤ ‖a-z‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    priceEnergy (energy Z) lam*formMass ψ ≤ formEnergy Z ψ + lam*N*formMass ψ +
      formMass ψ * (tfKinetic*(∫ z, (ρ z)^(5/3 : ℝ)) +
        (packetDirichlet g/2)*b⁻¹^2*(∫ z, ρ z) -
        (∫ y : Space, normalizedCoreField Z lam ψ y * ρ y) +
        (1/2:ℝ)*(∫ r : Space × Space, ρ r.1*ρ r.2/‖r.1-r.2‖)) := by
  rcases (formMass_nonneg ψ).eq_or_lt with hz | hmass
  · simpa only [←hz,mul_zero,zero_mul,add_zero] using hψ.priced_lower_bound hZ hlam
  · have hh := priced_patch_upper_comparison (hψ.normalize hmass) hm hn hJ hs hb hg hcg
      hgn hr hgs hpositive A (fun x i hi => (hcore x i hi).scale _) hsep hnuc hcs hZ hlam
    simp_rw [←normalizedCoreField_eq_scaled Z lam hmass] at hh
    have hh' := mul_le_mul_of_nonneg_right hh hmass.le
    rw [formEnergy_scale,inv_pow,Real.sq_sqrt hmass.le] at hh'
    refine hh'.trans_eq ?_
    field_simp
    ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_ConditionalPatchMinimizer
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
open scoped BigOperators ContDiff ENNReal

namespace CoulombAtom
open CoulombAnalysis

theorem conditional_priced_patch_minimizer_upper {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) (R : ℝ) (Φ : TFField R)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    (hΦ : Φ =ᵐ[ballMeasure R] fun x => normalizedCoreField Z lam ψ (y+x))
    {F : ℝ} (hF : ∀ᵐ x ∂ballMeasure R, Φ x ≤ F)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x : Space, (g x)^2 = 1) (hr : IsRadial g)
    (hgs : tsupport g ⊆ ball 0 1) {b : ℝ} (hb : 0 < b)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (hsep : Disjoint A (packetRegion (scaledRealPacket b g) (closedBall y R)))
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hcs : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖) :
    let f := tfPatchMinimizer R tfKinetic tfKinetic_pos Φ
    priceEnergy (energy Z) lam*formMass ψ ≤ formEnergy Z ψ+lam*N*formMass ψ+
      formMass ψ*(tfPatchFunctional R tfKinetic Φ f+
        (packetDirichlet g/2)*b⁻¹^2*(∫ x, f x ∂ballMeasure R)) := by
  let f := tfPatchMinimizer R tfKinetic tfKinetic_pos Φ
  let B := (max F 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)
  have hf : NonnegDensity f := tfPatchMinimizer_nonneg R tfKinetic tfKinetic_pos Φ
  have hB : ∀ᵐ x ∂ballMeasure R, f x ≤ B := tfPatchMinimizer_ae_bound tfKinetic_pos Φ hF
  have hh := conditional_priced_patch_upper hψ (translatedPatchDensity_measurable y R B f)
    (translatedPatchDensity_nonneg y R B f) (isCompact_closedBall y R)
    (translatedPatchDensity_support y R B f) (translatedPatchDensity_le y R B f)
    hg hcg hgn hr hgs hb A hcore hsep hnuc hcs hZ hlam
  rw [translatedPatchDensity_mass y hf hB,translatedPatchDensity_kinetic y hf hB,
    translatedPatchDensity_coulomb y hf hB,translatedPatchDensity_field y hf hB] at hh
  have he : (∫ x, normalizedCoreField Z lam ψ (y+x)*f x ∂ballMeasure R) =
      ∫ x, Φ x*f x ∂ballMeasure R := by
    apply integral_congr_ae
    filter_upwards [hΦ] with x hx
    rw [hx]
  rw [he] at hh
  simpa only [tfPatchFunctional,tfPatchLinear_apply,sub_eq_add_neg,add_assoc,
    add_left_comm,add_comm] using hh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_PatchRandomVariables
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
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombNeumann CoulombAnalysis

lemma conditionalPatchField_ae {N M : ℕ} (ψ : FormVector (N+M)) (t : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) (u : Configuration M)
    (hf : MemLp (fun z => normalizedCoreField Z lam (coreSlice ψ t u) (y+z)) (5/2) (ballMeasure R)) :
    conditionalPatchField ψ t Z lam y R u =ᵐ[ballMeasure R]
      fun z => normalizedCoreField Z lam (coreSlice ψ t u) (y+z) := by
  rw [conditionalPatchField,toLpOrZero_eq hf]
  exact hf.coeFn_toLp

attribute [local instance] OAI.CoulombAtom.instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFField_1
local instance instBorelSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFField_1_r394ffd_1 (R : ℝ) : BorelSpace (TFField R) := ⟨rfl⟩
attribute [local instance] OAI.CoulombAtom.instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_1
attribute [local instance] OAI.CoulombAtom.instBorelSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_1
lemma conditionalPatchMass_aemeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) (y : Space) (R : ℝ) :
    AEMeasurable (fun u => ∫ z, tfPatchMinimizer R tfKinetic tfKinetic_pos
      (conditionalPatchField ψ t Z lam y R u) z ∂ballMeasure R) :=
  (tfPatchIntegral_continuous R).measurable.comp_aemeasurable
    (conditionalPatchMinimizer_aemeasurable hψ t Z lam y R)

lemma conditionalPatchGap_aemeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) (y : Space) (R : ℝ)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    (hS : ∀ i, MeasurableSet {u | i ∈ S u}) :
    AEMeasurable (fun u => tfPatchGap R tfKinetic tfKinetic_pos
      (conditionalPatchField ψ t Z lam y R u) (retainedPatchLp hb (S u) u y R)) := by
  have hf : AEMeasurable (conditionalPatchField ψ t Z lam y R) :=
    conditionalPatchField_aemeasurable hψ t Z lam y R
  have hs : Measurable (fun u : Configuration M => retainedPatchLp hb (S u) u y R) :=
    retainedPatchLp_measurable hb S id hS measurable_id y R
  exact tfPatchGap_comp_aemeasurable R tfKinetic tfKinetic_pos _ _ hf hs.aemeasurable

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
section Work_ConditionalRetainedGap_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff ENNReal

open CoulombAnalysis CoulombNeumann

theorem conditional_retained_patch_gap {M N : ℕ} {ψ : FormVector M}
    (hψ : SobolevFermion ψ) (y : Space) (R : ℝ) (Φ : TFField R)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    (hΦ : Φ =ᵐ[ballMeasure R] fun z => normalizedCoreField Z lam ψ (y+z))
    {F : ℝ} (hF : ∀ᵐ z ∂ballMeasure R, Φ z ≤ F)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g)
    (hgs : tsupport g ⊆ ball 0 1) {b : ℝ} (hb : 0 < b)
    (A : Set Space) (hcore : ∀ u i, u i ∉ A → FormZeroAt ψ u)
    (hsep : Disjoint A (packetRegion (scaledRealPacket b g) (closedBall y R)))
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hcs : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖)
    (S : Finset (Fin N)) (x : Configuration N)
    (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R)
    (hret_nuc : ∀ i ∈ S, Real.sqrt 3*b ≤ ‖x i‖)
    (hret_core : ∀ i ∈ S, ∀ a ∈ A, Real.sqrt 3*b ≤ ‖a-x i‖) :
    let σ := retainedPatchLp hb S x y R
    let ρ := tfPatchMinimizer R tfKinetic tfKinetic_pos Φ
    formMass ψ*((1/2:ℝ)*tfCoulombL R (σ-ρ) (σ-ρ)+
      (∫ z, max (tfBallPotential R ρ z-Φ z) 0*σ z ∂ballMeasure R)) ≤
      formEnergy Z ψ+lam*M*formMass ψ-priceEnergy (energy Z) lam*formMass ψ+
        formMass ψ*(tfKinetic*retainedPressure b S x-
          (∑ i ∈ S, normalizedCoreField Z lam ψ (x i))+
          (1/2:ℝ)*(∫ p : Space × Space,
            retainedSmear b S x p.1*retainedSmear b S x p.2/‖p.1-p.2‖)+
          (packetDirichlet g/2)*b⁻¹^2*(∫ z, ρ z ∂ballMeasure R)) := by
  dsimp only
  have hu := conditional_priced_patch_minimizer_upper hψ y R Φ hZ hlam hΦ hF
    hg hcg hgn hr hgs hb A hcore hsep hnuc hcs
  have hg := mul_le_mul_of_nonneg_left
    (tfPatchFunctional_clipping_gap R Φ tfKinetic_pos (retainedPatchLp_nonneg hb S x y R))
    (formMass_nonneg ψ)
  rw [retainedPatchLp_functional hb S x y hmargin Φ (normalizedCoreField Z lam ψ) hΦ tfKinetic,
    retainedSmear_core_field hψ.sobolevVector hb S x A hcore hret_nuc hret_core Z lam] at hg
  dsimp only at hu
  nlinarith

end Work_ConditionalRetainedGap_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombNeumann

lemma conditionalPatchField_upper {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (y : Space) (R : ℝ) (Z lam : ℝ)
    {b : ℝ} (hb : 0 < b) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hcs : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖) :
    ∀ᵐ u : Configuration M, ∀ᵐ z ∂ballMeasure R,
      conditionalPatchField ψ t Z lam y R u z ≤ finiteCorePatchBound N Z lam b := by
  apply (hψ.ae_coreSlice t).mono
  intro u hu
  have hf := normalizedCoreField_memLp_patch hu A (hcore u) y R hb hb hnuc hcs Z lam
  filter_upwards [conditionalPatchField_ae ψ t Z lam y R u hf,
    ae_restrict_mem measurableSet_ball] with z hz hmem
  have hpos : y+z ∈ closedBall y R := by
    simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left] using
      ((mem_ball_zero_iff.mp hmem).le)
  rw [hz]
  exact (le_abs_self _).trans (normalizedCoreField_abs_le hu A (hcore u) hb (y+z)
    (fun a ha => hcs a ha _ hpos) hb (hnuc _ hpos) Z lam)

def weightedPatchMass {N M : ℕ} (ψ : FormVector (N+M)) (t : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) (u : Configuration M) : ℝ :=
  formMass (coreSlice ψ t u)*(∫ z,
    tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u) z ∂ballMeasure R)

lemma weightedPatchMass_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (y : Space) {R : ℝ} (hR : 0 < R) (Z lam : ℝ)
    {b : ℝ} (hb : 0 < b) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hcs : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖) :
    Integrable (weightedPatchMass ψ t Z lam y R) := by
  have hm := (conditionalPatchMass_aemeasurable hψ t Z lam y R).aestronglyMeasurable
  have hbnd : ∀ᵐ u : Configuration M, ‖(∫ z,
      tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u) z ∂ballMeasure R)‖ ≤
      4*R*finiteCorePatchBound N Z lam b := by
    apply (conditionalPatchField_upper hψ t y R Z lam hb A hcore hnuc hcs).mono
    intro u hu
    rw [Real.norm_of_nonneg (integral_nonneg_of_ae (tfPatchMinimizer_nonneg R tfKinetic tfKinetic_pos _))]
    exact tfPatchMinimizer_mass_le hR tfKinetic_pos (finiteCorePatchBound_nonneg N Z lam hb) _ hu
  exact ((hψ.coreSlice_mass_integrable t).bdd_mul hm hbnd).congr
    (Eventually.of_forall fun _ => mul_comm _ _)

lemma coreSlice_priceExcess_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) :
    Integrable (fun u => corePriceExcess Z lam (coreSlice ψ t u)) := by
  exact ((hψ.coreSlice_energy_integrable Z t).add ((hψ.coreSlice_mass_integrable t).const_mul (lam*N))).sub
    ((hψ.coreSlice_mass_integrable t).const_mul (priceEnergy (energy Z) lam))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_OutCutAntisymmetry
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma swapBlocks_ordered_value {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a : Fin 2, (p a).value x^2 = 1) (ψ : FormVector L)
    (c : Fin L → Fin 2) (s) (x) :
    (swapBlocks (orderedCutForm p hp ψ c)).value s x =
      (multiplyForm (spatialProduct p hp (outFirstLabels (cutCoreNumber c) (cutOutNumber c)))
        (reindexForm ((blockSwap (cutCoreNumber c) (cutOutNumber c)).trans (cutOrder c)) ψ)).value s x := by
  change (spatialProductValue p c ((x ∘ (blockSwap _ _).symm) ∘ (cutOrder c).symm) : ℂ) * _ = _
  rw [spatialProductValue_reindex,spatialProductValue_reindex,cutOrder_labels,coreCutLabels_blockSwap]
  rfl

lemma orderedCutForm_out_antisymmetric {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a : Fin 2, (p a).value x^2 = 1)
    {ψ : FormVector L} (hψ : SobolevFermion ψ) (c : Fin L → Fin 2) :
    CoreAntisymmetric (swapBlocks (orderedCutForm p hp ψ c)) := by
  have ha := (hψ.reindex ((blockSwap _ _).trans (cutOrder c))).coreAntisymmetric.multiply
    (spatialProduct p hp (outFirstLabels (cutCoreNumber c) (cutOutNumber c)))
    (fun π x => spatialProduct_invariant p _ (corePerm _ π) (outFirstLabels_invariant π) x)
  intro π s
  simpa only [swapBlocks_ordered_value] using ha π s

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_OutRetainedLower
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
section Work_OutRetainedLower_scope

open MeasureTheory Filter Set
open scoped BigOperators

open CoulombNeumann CoulombAnalysis

lemma out_retained_kinetic {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (ha : CoreAntisymmetric (swapBlocks ψ))
    {b : ℝ} (hb : 0 < b)
    (S : Spins M → Configuration M → Finset (Fin M))
    (hS : ∀ t i, MeasurableSet {x | i ∈ S t x}) :
    tfKinetic*(∑ t : Spins M, ∫ x : Configuration M,
      retainedPressure b (S t x) x*formMass (coreSlice ψ t x)) ≤
      outKinetic ψ+b⁻¹^2*neumannRemainderConstant*((M:ℝ)^(4/3:ℝ)+(M:ℝ))*formMass ψ := by
  have hs (t : Spins M) (i : Fin M) : MeasurableSet {p : Configuration M × Configuration N | i ∈ S t p.1} :=
    measurable_fst (hS t i)
  have hh := ha.neumann_retained_slices (swapBlocks_sobolev hψ) hb
    (fun _ t p => S t p.1) (fun _ t i => hs t i)
  rw [weighted_coreSlice_reorder ψ (fun t x => retainedPressure b (S t x) x)
    (fun s t => retained_pressure_join_integrable (swapBlocks_sobolev hψ) hb
      (fun p => S s p.1) (hs s) s t),swapBlocks_coreKinetic,swapBlocks_mass] at hh
  exact hh

lemma out_retained_repulsion {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (ha : CoreAntisymmetric (swapBlocks ψ))
    {b : ℝ} (hb : 0 < b)
    (S : Spins M → Configuration M → Finset (Fin M))
    (hS : ∀ t i, MeasurableSet {x | i ∈ S t x}) :
    (∑ t : Spins M, ∫ x : Configuration M,
      retainedDirect b (S t x) x*formMass (coreSlice ψ t x)) ≤
      outRepulsion ψ+(((2*Real.pi+1)/2)*(M:ℝ)/b)*formMass ψ := by
  have hs (t : Spins M) (i : Fin M) : MeasurableSet {p : Configuration M × Configuration N | i ∈ S t p.1} :=
    measurable_fst (hS t i)
  have hh := ha.retained_repulsion_slices (swapBlocks_sobolev hψ) hb
    (fun _ t p => S t p.1) (fun _ t i => hs t i)
  rw [weighted_coreSlice_reorder ψ (fun t x => retainedDirect b (S t x) x)
    (fun s t => retained_direct_join_integrable (swapBlocks_sobolev hψ) hb
      (fun p => S s p.1) (hs s) s t),swapBlocks_coreRepulsion,swapBlocks_mass] at hh
  exact hh

end Work_OutRetainedLower_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombNeumann

lemma integral_coreSlice_priceExcess {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam : ℝ) :
    (∑ t : Spins M, ∫ u, corePriceExcess Z lam (coreSlice ψ t u)) =
      (∑ t : Spins M, ∫ u, formEnergy Z (coreSlice ψ t u)+
        lam*N*formMass (coreSlice ψ t u))-priceEnergy (energy Z) lam*formMass ψ := by
  have he (t : Spins M) : (∫ u, corePriceExcess Z lam (coreSlice ψ t u)) =
      (∫ u, formEnergy Z (coreSlice ψ t u)+lam*N*formMass (coreSlice ψ t u))-
        priceEnergy (energy Z) lam*(∫ u, formMass (coreSlice ψ t u)) := by
    unfold corePriceExcess
    have he := integral_sub ((hψ.coreSlice_energy_integrable Z t).add
      ((hψ.coreSlice_mass_integrable t).const_mul (lam*N)))
      ((hψ.coreSlice_mass_integrable t).const_mul (priceEnergy (energy Z) lam))
    simp only [Pi.add_apply,integral_const_mul] at he
    exact he
  simp_rw [he]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,hψ.integral_coreSlice_mass]

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

lemma radialPatch_packet_separation (y : Space) {t b : ℝ} (hb : 0 < b)
    {g : Space → ℝ} (hgs : tsupport g ⊆ ball 0 1) :
    Disjoint (radialPatchCore y t)
      (packetRegion (scaledRealPacket b g) (closedBall y (t-4*b))) := by
  rw [Set.disjoint_left]
  rintro x hx ⟨⟨w,z⟩,⟨hw,hz⟩,rfl⟩
  have hw' := scaledRealPacket_tsupport hb hgs hw
  simp only [mem_closedBall,dist_zero_right] at hw'
  simp only [mem_closedBall,dist_eq_norm] at hz
  have hh : ‖w+z-y‖ ≤ ‖w‖+‖z-y‖ := by
    simpa only [add_sub_assoc] using norm_add_le w (z-y)
  change t ≤ ‖w+z-y‖ at hx
  linarith

lemma radialPatch_core_distance (y : Space) {t b : ℝ} (hb : 0 < b)
    (a : Space) (ha : a ∈ radialPatchCore y t) (z : Space)
    (hz : z ∈ closedBall y (t-4*b)) : b ≤ ‖a-z‖ := by
  change t ≤ ‖a-y‖ at ha
  simp only [mem_closedBall,dist_eq_norm] at hz
  have hh := dist_triangle a z y
  simp only [dist_eq_norm] at hh
  linarith

lemma radialPatch_retained_core {L : ℕ} (y : Space) {t b : ℝ} (hb : 0 < b)
    (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) (u : Configuration (cutOutNumber c))
    (i : Fin (cutOutNumber c)) (hi : i ∈ radialPatchRetention L y t b c s u)
    (a : Space) (ha : a ∈ radialPatchCore y t) : Real.sqrt 3*b ≤ ‖a-u i‖ := by
  have hi' : ‖u i-y‖ < t-7*b := (Finset.mem_filter.mp hi).2
  have hs := mul_le_mul_of_nonneg_right sqrt_three_le_three hb.le
  change t ≤ ‖a-y‖ at ha
  have hh := dist_triangle a (u i) y
  simp only [dist_eq_norm] at hh
  linarith

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombNeumann

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CutOuterLaw
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

lemma outProjection_measurable (N M : ℕ) :
    Measurable (outProjection (N := N) (M := M)) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

lemma weighted_coreSlice_eq_full {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) {g : Configuration M → ℝ} (hg : Measurable g)
    {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) :
    (∑ s : Spins M, ∫ u, g u*formMass (coreSlice ψ s u)) =
      ∑ s : Spins (N+M), ∫ x, g (outProjection x)*‖ψ.value s x‖^2 := by
  have hi (s : Spins (N+M)) : Integrable (fun x => g (outProjection x)*‖ψ.value s x‖^2) :=
    ((hψ.1 s).norm.integrable_sq).bdd_mul
      (hg.comp (outProjection_measurable N M)).aestronglyMeasurable (ae_of_all _ (fun x => hB _))
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

lemma cutOutPositions_reindex {L : ℕ} (c : Fin L → Fin 2)
    (x : Configuration (cutCoreNumber c+cutOutNumber c)) :
    cutOutPositions c (x ∘ (cutOrder c).symm) = outProjection x := by
  ext i
  simp only [cutOutPositions,Function.comp_apply,Equiv.symm_apply_apply,outProjection]

lemma cutOuter_expectation_eq_full {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L} (hψ : SobolevVector ψ)
    (c : Fin L → Fin 2) {g : Configuration (cutOutNumber c) → ℝ} (hg : Measurable g)
    {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) :
    (∑ s : Spins (cutOutNumber c), ∫ u,
      g u*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) =
      ∑ s : Spins L, ∫ x, g (cutOutPositions c x)*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2 := by
  rw [weighted_coreSlice_eq_full (orderedCutForm_sobolev p hp hψ c) hg hB]
  have he (s : Spins (cutCoreNumber c+cutOutNumber c)) :
      (∫ x, g (outProjection x)*‖(orderedCutForm p hp ψ c).value s x‖^2) =
      ∫ x, g (cutOutPositions c x)*‖(multiplyForm (spatialProduct p hp c) ψ).value
        (s ∘ (cutOrder c).symm) x‖^2 := by
    simpa only [orderedCutForm,reindexForm,cutOutPositions_reindex] using
      integral_reindex (cutOrder c) (fun x => g (cutOutPositions c x)*
        ‖(multiplyForm (spatialProduct p hp c) ψ).value (s ∘ (cutOrder c).symm) x‖^2)
  simp_rw [he]
  exact sum_spin_reindex (cutOrder c) (fun s : Spins L =>
    ∫ x, g (cutOutPositions c x)*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2)

lemma outerDeleted_second_moment_eq_cut {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) (t b : ℝ) :
    (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      outerDeletedCount y t b u^2*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) =
      spatialCutExpectation p hp ψ (fun c x => cutDeletedCount y t b c x^2) := by
  unfold spatialCutExpectation
  apply Finset.sum_congr rfl; intro c _
  rw [cutOuter_expectation_eq_full p hp hψ c ((outerDeletedCount_measurable y t b).pow_const 2)
    (fun u => norm_sq_le_of_nonneg (outerDeletedCount_nonneg _ _ _ _) (outerDeletedCount_le _ _ _ _))]
  simp only [outerDeletedCount_cutOutPositions]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_QuantumMultiplierLaw
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

def quantumObservationEvent {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) (s : Set (J × (Fin N × Fin 3) → ℝ)) :
    Set (Configuration N × (J × (Fin N × Fin 3) → ℝ)) :=
  {z | observationPlacement b (flattenConfiguration N z.1) + z.2 ∈ s}

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_DyadicObservation
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

def physicalObservationEvent {N : ℕ} {J : Type*} [Fintype J]
    (ell : J → ℝ) (s : Set (J × (Fin N × Fin 3) → ℝ)) :
    Set (Configuration N × (J × (Fin N × Fin 3) → ℝ)) :=
  physicalObservationArray ell ⁻¹' s

def physicalObservationProbability {N : ℕ} {J : Type*} [Fintype J]
    (F : fermionGraph N) (ell : J → ℝ) (s : Set (J × (Fin N × Fin 3) → ℝ)) : ℝ :=
  (((graphRawLaw F).prod (Measure.pi (fun _ : J × (Fin N × Fin 3) => compactNoiseLaw)))
    (physicalObservationEvent ell s)).toReal

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_UnorderedObservations
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter Metric
open scoped BigOperators NNReal

namespace CoulombAtom
open CoulombObservation

def observedLocalCount {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K)
    (y : Space) (R : ℝ) (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) : ℝ :=
  ∑ i, if ‖physicalObservedConfiguration ell k z i-y‖ ≤ R then 1 else 0

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ConditionalSandwich
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter

open MeasureTheory Filter Set Metric
open scoped BigOperators NNReal

namespace CoulombAtom
open CoulombObservation

def posteriorTestValue {N K : ℕ} (μ : Measure (Configuration N)) (ell : Fin K → ℝ)
    (j : ℕ) (g : Space → ℝ) :
    (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → ℝ :=
  (physicalObservationLaw μ K)[(fun z => ∑ i, g (z.1 i)) | observationInformation ell j]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_OriginalPosteriorKernel
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

instance originalRawKernel_markov {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) :
    IsMarkovKernel (originalRawKernel μ ell j) := by
  unfold originalRawKernel
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_LocalWidthKernel
attribute [-instance] _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma scaledRealPacket_sq {b : ℝ} (hb : 0 < b) (g : Space → ℝ) (z : Space) :
    (scaledRealPacket b g z)^2 = b⁻¹^3*(g (b⁻¹ • z))^2 := by
  have he : (b ^(-(3/2:ℝ)))^2 = b⁻¹^3 := by
    apply mul_right_cancel₀ (pow_ne_zero 3 hb.ne')
    rw [packetScale_factor hb,←mul_pow,inv_mul_cancel₀ hb.ne',one_pow]
  simp only [scaledRealPacket,mul_pow,he]

lemma masterKernel_eq_widthKernel {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) (g : Space → ℝ) :
    masterKernel c₁ r₀ s g = widthKernel (masterWidth c₁ r₀ s) (fun z => (g z)^2) := by
  funext x y
  exact scaledRealPacket_sq (masterWidth_pos hc hr hs x) g (y-x)

lemma masterWidth_small_lipschitz {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) :
    LipschitzWith (1/2) (masterWidth c₁ r₀ s) := by
  apply (masterWidth_lipschitz hc.le hr hs).weaken
  change c₁*(1+masterExponent)*s^masterExponent ≤ (1/2:ℝ)
  have hp := Real.rpow_le_one hs.le hs1 masterExponent_nonneg
  have hcp : 0 ≤ c₁*(1+masterExponent) := mul_nonneg hc.le (by linarith [masterExponent_pos])
  calc
    _ ≤ c₁*(1+masterExponent)*1 := mul_le_mul_of_nonneg_left hp hcp
    _ ≤ _ := by norm_num [masterExponent] at *; nlinarith

lemma masterProfile_support {g : Space → ℝ} (hgs : tsupport g ⊆ ball 0 1) :
    Function.support (fun z => (g z)^2) ⊆ closedBall 0 1 := by
  intro z hz
  have hg : g z ≠ 0 := by intro H; exact hz (by simp [H])
  exact ball_subset_closedBall (hgs (subset_tsupport g hg))

theorem masterKernel_uniform_test_constants {g : Space → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgs : tsupport g ⊆ ball 0 1) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (c₁ r₀ s : ℝ),
      0 < c₁ → c₁ < (10*(100000:ℝ))⁻¹ → 0 < r₀ → 0 < s → s ≤ 1 →
      ∀ y : Space,
      Function.support (fun x => masterKernel c₁ r₀ s g x y) ⊆
        closedBall y (2*masterWidth c₁ r₀ s y) ∧
      LipschitzWith ⟨(C:ℝ)*(masterWidth c₁ r₀ s y)⁻¹^4, by positivity⟩
        (fun x => masterKernel c₁ r₀ s g x y) := by
  have hp := masterProfile_support hgs
  have hcomp : HasCompactSupport (fun z => (g z)^2) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space) 1) hp
  obtain ⟨H,hH⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcomp (hg.pow 2) (by simp)
  obtain ⟨z₀,hz₀⟩ := (hg.continuous.pow 2).norm.exists_forall_ge_of_hasCompactSupport hcomp.norm
  let M := ‖(g z₀)^2‖
  have hM : 0 ≤ M := norm_nonneg _
  refine ⟨⟨24*M+24*(H:ℝ)+1,by positivity⟩,?_,?_⟩
  · change (0:ℝ) < 24*M+24*(H:ℝ)+1
    positivity
  intro c₁ r₀ s hc hcL hr hs hs1 y
  rw [masterKernel_eq_widthKernel hc hr hs g]
  have ht := masterWidth_small_lipschitz hc hcL hr hs hs1
  have hpos := masterWidth_pos hc hr hs
  refine ⟨widthKernel_support_local ht hpos (by norm_num) hp y,?_⟩
  apply (widthKernel_local_lipschitz ht hpos (by norm_num) hH hM hz₀ hp y).weaken
  change (24*M+24*(H:ℝ))*(masterWidth c₁ r₀ s y)⁻¹^4 ≤
    (24*M+24*(H:ℝ)+1)*(masterWidth c₁ r₀ s y)⁻¹^4
  exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (inv_nonneg.mpr (hpos y).le) 4)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_CutMomentBounds
attribute [-instance] _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

lemma cutOutMoment_le_second {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector N} (hψ : SobolevVector ψ)
    (hm : formMass ψ = 1) {r : ℝ} (hr : 0 ≤ r) (hr2 : r ≤ 2) :
    (∑ c : Fin N → Fin 2, (cutOutNumber c:ℝ)^r*formMass (orderedCutForm p hp ψ c)) ≤
      (∑ c : Fin N → Fin 2, (cutOutNumber c:ℝ)^2*formMass (orderedCutForm p hp ψ c))^(r/2) := by
  have hh := (Real.concaveOn_rpow (p := r/2) (by positivity) (by linarith)).le_map_sum
    (t := Finset.univ) (w := fun c : Fin N → Fin 2 => formMass (orderedCutForm p hp ψ c))
    (p := fun c => (cutOutNumber c:ℝ)^2)
    (fun c _ => formMass_nonneg _) ((orderedCutForm_mass_sum p hp hψ).trans hm)
    (fun c _ => sq_nonneg (cutOutNumber c:ℝ))
  have he (c : Fin N → Fin 2) : ((cutOutNumber c:ℝ)^2)^(r/2) = (cutOutNumber c:ℝ)^r := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  simpa only [smul_eq_mul,he,mul_comm] using hh

lemma cutOutMoment_le_bound {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector N} (hψ : SobolevVector ψ)
    (hm : formMass ψ = 1) {r : ℝ} (hr : 0 ≤ r) (hr2 : r ≤ 2) {B : ℝ}
    (hB : (∑ c : Fin N → Fin 2, (cutOutNumber c:ℝ)^2*formMass (orderedCutForm p hp ψ c)) ≤ B) :
    (∑ c : Fin N → Fin 2, (cutOutNumber c:ℝ)^r*formMass (orderedCutForm p hp ψ c)) ≤ B^(r/2) :=
  (cutOutMoment_le_second p hp hψ hm hr hr2).trans
    (Real.rpow_le_rpow (Finset.sum_nonneg (fun c _ => mul_nonneg (sq_nonneg _) (formMass_nonneg _)))
      hB (by positivity))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_IntegratedLipschitzControl
attribute [-instance] _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped BigOperators ENNReal NNReal ContDiff

namespace CoulombAtom
open CoulombNeumann CoulombAnalysis

def weightedPatchTestSquare {N M : ℕ} (ψ : FormVector (N+M)) (s : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (g : TFSpace → ℝ)
    (u : Configuration M) : ℝ :=
  formMass (coreSlice ψ s u)*
    (∫ x, g x*(retainedPatchLp hb (S u) u y R-
      tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ s Z lam y R u)) x
        ∂ballMeasure R)^2

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_ExpectedTruncatedControl
attribute [-instance] _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ExpectedTruncatedControl_scope

open MeasureTheory Set Metric
open scoped BigOperators ENNReal NNReal ContDiff

open CoulombNeumann CoulombAnalysis

def weightedPatchTestAbs {N M : ℕ} (ψ : FormVector (N+M)) (s : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (g : TFSpace → ℝ)
    (u : Configuration M) : ℝ :=
  formMass (coreSlice ψ s u)*
    |∫ x, g x*(retainedPatchLp hb (S u) u y R-
      tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ s Z lam y R u)) x
        ∂ballMeasure R|

end Work_ExpectedTruncatedControl_scope

open MeasureTheory Filter Set Metric
open scoped ENNReal ContDiff

open CoulombAnalysis

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierTruncationBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierTruncation_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis
attribute [local irreducible] masterKernel masterWidth scaledRealPacket

def innerPotential (r : ℝ) (ρ : Space → ℝ) (y : Space) : ℝ :=
  ∫ z in ball (0 : Space) r, ρ z/‖y-z‖

end CoulombAtom

end Work_BarrierTruncation_barrier_scope

open Set Filter MeasureTheory Laplacian Metric ProbabilityTheory
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_MasterRecovery
attribute [-instance] _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped NNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis

noncomputable def masterTestConstant {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : tsupport g ⊆ ball 0 1) : ℝ≥0 :=
  (masterKernel_uniform_test_constants hg hgs).choose

def masterCenteredKernel (c₁ r₀ s : ℝ) (g : Space → ℝ) (y x : Space) : ℝ :=
  masterKernel c₁ r₀ s g (y+x) y

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_FreshPosteriorSandwich
attribute [-instance] _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.rotationMeasureHaar
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
open scoped BigOperators NNReal ContDiff

open CoulombObservation CoulombNeumann CoulombAnalysis

def masterPosterior {N K : ℕ} (μ : Measure (Configuration N)) (ell : Fin K → ℝ)
    (j : ℕ) (c₁ r₀ s : ℝ) (g : Space → ℝ)
    (z : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))) (y : Space) : ℝ :=
  posteriorTestValue μ ell j (fun x => masterKernel c₁ r₀ s g x y) z

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierMasterRegularityBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierMasterRegularity_barrier_scope

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators ContDiff Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombObservation

attribute [local irreducible] masterKernel masterWidth scaledRealPacket

def masterConfigurationDensity {N : ℕ} (c₁ r₀ s : ℝ) (g : Space → ℝ)
    (z : Configuration N) (y : Space) : ℝ := ∑ i, masterKernel c₁ r₀ s g (z i) y

end CoulombBarrier

end Work_BarrierMasterRegularity_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierObservationTowerBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] masterKernel masterWidth scaledRealPacket

def originalMasterField {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (c₁ r₀ s : ℝ) (g : Space → ℝ)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) (y : Space) : ℝ :=
  jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z) y

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_DeletedFieldBudget
attribute [-instance] _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

lemma weighted_outerDeleted_sq_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (y : Space) (t b : ℝ) :
    Integrable (fun u => outerDeletedCount y t b u^2*formMass (coreSlice ψ s u)) := by
  exact (hψ.coreSlice_mass_integrable s).bdd_mul
    ((outerDeletedCount_measurable y t b).pow_const 2).aestronglyMeasurable
    (ae_of_all _ (fun u => norm_sq_le_of_nonneg (outerDeletedCount_nonneg _ _ _ _) (outerDeletedCount_le _ _ _ _)))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_ConditionalPatchPDE
attribute [-instance] _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis

theorem conditionalPatchMinimizer_weak_pde {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) (R : ℝ) {d r : ℝ} (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖)
    (Z lam : ℝ) {g : Space → ℝ} (hg : ContDiff ℝ 2 g)
    (hcg : HasCompactSupport g) (hs : tsupport g ⊆ ball 0 R) :
    let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
    let W := fun x => normalizedCoreField Z lam (coreSlice ψ t u) (y+x)-tfBallPotential R f x
    (∫ x, W x*Δ g x ∂ballMeasure R) = 4*Real.pi*
      (∫ x, (max (W x) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*g x ∂ballMeasure R) := by
  let Φ := conditionalPatchField ψ t Z lam y R u
  let f := tfPatchMinimizer R tfKinetic tfKinetic_pos Φ
  let V := fun x => normalizedCoreField Z lam (coreSlice ψ t u) (y+x)
  let W := fun x => V x-tfBallPotential R f x
  change (∫ x, W x*Δ g x ∂ballMeasure R) = _
  have hp : MemLp V (5/2) (ballMeasure R) :=
    normalizedCoreField_memLp_patch hu A hcore y R hd hr hnuc hsep Z lam
  have he : Φ =ᵐ[ballMeasure R] V := conditionalPatchField_ae ψ t Z lam y R u hp
  have h0 : (0 : Space) ∉ ball y R := by
    intro hn
    have hh := hnuc 0 (ball_subset_closedBall hn)
    simp only [norm_zero] at hh
    linarith
  have hA : ∀ a ∈ A, a ∉ ball y R := by
    intro a ha hn
    have hh := hsep a ha a (ball_subset_closedBall hn)
    simp only [sub_self,norm_zero] at hh
    linarith
  have hharm : (∫ x, V x*Δ g x ∂ballMeasure R) = 0 :=
    normalizedCoreField_weak_harmonic_ball hu A hcore y R h0 hA hg hcg hs Z lam
  have hlp : MemLp (Δ g) (5/3) (ballMeasure R) :=
    ((tfLaplacian_continuous hg).memLp_of_hasCompactSupport (tfLaplacian_compact hg hcg)
      (μ := volume)).mono_measure Measure.restrict_le_self
  have hi : Integrable (fun x => V x*Δ g x) (ballMeasure R) := hp.integrable_mul hlp
  have hi' := tfBallPotential_laplacian_integrable R f hg hcg hs
  have heuler : ∀ᵐ x ∂ballMeasure R, f x =
      (max (W x) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ) := by
    filter_upwards [tfPatchFunctional_euler R Φ tfKinetic_pos
      (tfPatchMinimizer_nonneg R tfKinetic tfKinetic_pos Φ)
      (fun g hg => tfPatchMinimizer_min R tfKinetic tfKinetic_pos Φ hg),he] with x hx hΦ
    simpa only [hΦ] using hx
  calc
    _ = (∫ x, V x*Δ g x ∂ballMeasure R)-
        (∫ x, tfBallPotential R f x*Δ g x ∂ballMeasure R) := by
      simp only [W,sub_mul]
      exact integral_sub hi hi'
    _ = 4*Real.pi*(∫ x, f x*g x ∂ballMeasure R) := by
      rw [hharm,tfBallPotential_weak_laplacian R f hg hcg hs]
      ring
    _ = _ := by
      congr 1
      exact integral_congr_ae (heuler.mono fun x hx => by simp only [hx]; rfl)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_ActualPatchCap
attribute [-instance] _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

theorem conditionalPatchMinimizer_nonradial_cap {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R d r : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖)
    (Z lam : ℝ) (x : Space) (hx : ‖x‖ ≤ 3*R/4) :
    let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
    normalizedCoreField Z lam (coreSlice ψ t u) (y+x)-tfBallPotential R f x ≤
      tfPatchCapConstant/R^4 := by
  let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
  apply weak_tf_nonradial_cap hR tfReactionCoefficient_pos
    (actualPatchField_continuousOn hu A hcore y R hd hr hnuc hsep Z lam f) _ x hx
  intro g hg hcg hs
  apply tf_weak_pde_volume _ hg hcg hs
  intro g hg hcg hs
  exact conditionalPatchMinimizer_weak_pde ψ t u hu A hcore y R hd hr hnuc hsep Z lam hg hcg hs

theorem conditionalPatchMinimizer_density_cap {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R d r : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖) (Z lam : ℝ) :
    let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
    ∀ᵐ x ∂ballMeasure R, ‖x‖ ≤ 3*R/4 →
      f x ≤ (tfPatchCapConstant/R^4/((5/3:ℝ)*tfKinetic))^(3/2:ℝ) := by
  let Φ := conditionalPatchField ψ t Z lam y R u
  let f := tfPatchMinimizer R tfKinetic tfKinetic_pos Φ
  have hp := normalizedCoreField_memLp_patch hu A hcore y R hd hr hnuc hsep Z lam
  have hΦ := conditionalPatchField_ae ψ t Z lam y R u hp
  filter_upwards [tfPatchFunctional_euler R Φ tfKinetic_pos
    (tfPatchMinimizer_nonneg R tfKinetic tfKinetic_pos Φ)
    (fun g hg => tfPatchMinimizer_min R tfKinetic tfKinetic_pos Φ hg),hΦ] with x he hΦx
  intro hx
  rw [he,hΦx]
  apply Real.rpow_le_rpow (div_nonneg (le_max_right _ _) (mul_nonneg (by norm_num) tfKinetic_pos.le)) _ (by norm_num)
  apply div_le_div_of_nonneg_right _ (mul_nonneg (by norm_num) tfKinetic_pos.le)
  exact max_le (conditionalPatchMinimizer_nonradial_cap ψ t u hu A hcore y hR hd hr hnuc hsep Z lam x hx)
    (div_nonneg tfPatchCapConstant_pos.le (pow_nonneg hR.le _))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RootMomentCauchyBarrier
attribute [-instance] _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

lemma localCellRadius_near {y v : Space} (hy : y ≠ 0) (hv : ‖v‖ ≤ 32) :
    localCellRadius y/2 ≤ localCellRadius (y+localCellRadius y • v) ∧
      localCellRadius (y+localCellRadius y • v) ≤ 2*localCellRadius y := by
  have ha := (localCellRadius_pos hy).le
  have hv' : ‖localCellRadius y • v‖ ≤ 32*localCellRadius y := by
    rw [norm_smul,Real.norm_of_nonneg ha]
    nlinarith
  have hu := norm_add_le y (localCellRadius y • v)
  have hl : ‖y‖ ≤ ‖y+localCellRadius y • v‖+‖localCellRadius y • v‖ := by
    calc ‖y‖ = ‖(y+localCellRadius y • v)-localCellRadius y • v‖ := by rw [add_sub_cancel_right]
         _ ≤ _ := norm_sub_le _ _
  unfold localCellRadius at *
  constructor <;> linarith

lemma localOffsetMass_near {D : ℝ} (hD : 0 ≤ D) {y v : Space}
    (hy : y ≠ 0) (hv : ‖v‖ ≤ 32) :
    localOffsetMass D (y+localCellRadius y • v) ≤ 8*localOffsetMass D y := by
  let a := localCellRadius y
  let z := y+a • v
  have ha : 0 < a := localCellRadius_pos hy
  have hnear := localCellRadius_near hy hv
  have hz : 0 < localCellRadius z := lt_of_lt_of_le (show 0 < a/2 by positivity) hnear.1
  have hc : 1/(localCellRadius z)^3 ≤ 8/a^3 := by
    calc 1/(localCellRadius z)^3 ≤ 1/(a/2)^3 :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hnear.1 3)
         _ = _ := by ring
  have hm : max (1/(localCellRadius z)^3) 1 ≤ 8*max (1/a^3) 1 := by
    apply max_le
    · exact hc.trans (by convert mul_le_mul_of_nonneg_left (le_max_left (1/a^3) 1) (by norm_num : (0:ℝ) ≤ 8) using 1; ring)
    · nlinarith [le_max_right (1/a^3) 1]
  have hs : Real.sqrt (D*localCellRadius z) ≤ 2*Real.sqrt (D*a) := by
    have hDs : 0 ≤ D*localCellRadius z := mul_nonneg hD hz.le
    have hDa : 0 ≤ D*a := mul_nonneg hD ha.le
    have hmul := mul_le_mul_of_nonneg_left hnear.2 hD
    nlinarith [Real.sq_sqrt hDs,Real.sq_sqrt hDa,
      Real.sqrt_nonneg (D*localCellRadius z),Real.sqrt_nonneg (D*a)]
  change max (1/(localCellRadius z)^3) 1+Real.sqrt (D*localCellRadius z) ≤
    8*(max (1/a^3) 1+Real.sqrt (D*a))
  linarith [Real.sqrt_nonneg (D*a)]

lemma localCountStencil_scaled_cover {y : Space} (hy : y ≠ 0) {x : Space}
    (hx : ‖x-y‖ < 32*localCellRadius y) :
    ∃ v ∈ localCountStencil, ‖x-(y+localCellRadius y • v)‖ <
      localCellRadius (y+localCellRadius y • v) := by
  let a := localCellRadius y
  have ha : 0 < a := localCellRadius_pos hy
  let u := a⁻¹ • (x-y)
  have hun : ‖u‖ = ‖x-y‖/a := by
    dsimp [u]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr ha.le)]
    ring
  have hu : ‖u‖ ≤ 32 := by rw [hun]; exact (div_le_iff₀ ha).mpr (by linarith)
  obtain ⟨v,hv,hv'⟩ := localCountStencil_cover hu
  refine ⟨v,hv,?_⟩
  have he : a • u = x-y := by dsimp [u]; rw [smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
  have he' : x-(y+a • v) = a • (u-v) := by rw [smul_sub,he]; abel
  rw [show localCellRadius y = a from rfl,he',norm_smul,Real.norm_of_nonneg ha.le]
  have hn := (localCellRadius_near hy (localCountStencil_norm hv)).1
  nlinarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SelectedPatchBudget
attribute [-instance] _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

def freshPatchMass {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector L)
    (Z lam : ℝ) (y : Space) (R : ℝ) : ℝ :=
  ∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
    weightedPatchMass (orderedCutForm p hp ψ c) s Z lam y R u

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CellCountSupremumBarrier
attribute [-instance] _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

def localCountRatioSet {N : ℕ} (ψ : FormVector N) (D : ℝ) : Set ℝ :=
  {q | ∃ y : Space, y ≠ 0 ∧ q = rawCountMoment ψ y (localCellRadius y)/(localOffsetMass D y)^2}

def localCountSupremum {N : ℕ} (ψ : FormVector N) (D : ℝ) : ℝ :=
  max 1 (sSup (localCountRatioSet ψ D))

lemma localCountRatioSet_nonempty {N : ℕ} (ψ : FormVector N) (D : ℝ) :
    (localCountRatioSet ψ D).Nonempty := by
  obtain ⟨y,hy⟩ := exists_ne (0 : Space)
  exact ⟨_,y,hy,rfl⟩

lemma localCountSupremum_one_le {N : ℕ} (ψ : FormVector N) (D : ℝ) :
    1 ≤ localCountSupremum ψ D := le_max_left _ _

lemma localCountSupremum_le {N : ℕ} {ψ : FormVector N} (D : ℝ) {C : ℝ}
    (hC : 1 ≤ C) (h : ∀ y : Space, y ≠ 0 →
      rawCountMoment ψ y (localCellRadius y) ≤ C*(localOffsetMass D y)^2) :
    localCountSupremum ψ D ≤ C := by
  apply max_le hC
  apply csSup_le (localCountRatioSet_nonempty ψ D)
  rintro q ⟨y,hy,rfl⟩
  have hm := localOffsetMass_one_le D y
  exact (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < localOffsetMass D y))).mpr (h y hy)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CellScaleBarrier
attribute [-instance] _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

lemma localOffsetMass_offset {D : ℝ} (hD : 0 ≤ D) {y : Space} (hy : y ≠ 0) :
    D*localCellRadius y ≤ (localOffsetMass D y)^2 := by
  have ha := localCellRadius_pos hy
  have h0 : 0 ≤ max (1/localCellRadius y^3) 1 := le_trans zero_le_one (le_max_right _ _)
  have hs := Real.sq_sqrt (mul_nonneg hD ha.le)
  have hn := Real.sqrt_nonneg (D*localCellRadius y)
  unfold localOffsetMass
  nlinarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PatchLocalObservable
attribute [-instance] _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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
open CoulombAnalysis CoulombNeumann

def weightedPatchLocalPotential {N M : ℕ} (ψ : FormVector (N+M)) (s : Spins M)
    (y : Space) (R q : ℝ) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (u : Configuration M) : ℝ :=
  formMass (coreSlice ψ s u)*
    (∫ x in ball 0 q, ‖retainedPatchLp hb (S u) u y R x‖/‖x‖)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_ActualMasterCenterComparison
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
open CoulombAnalysis CoulombObservation

instance graphRawLaw_finite {N : ℕ} (F : fermionGraph N) : IsFiniteMeasure (graphRawLaw F) := by
  constructor
  rw [graphRawLaw_univ]
  exact ENNReal.ofReal_lt_top

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

def exteriorCoordinates {N M : ℕ} (x : Configuration (N+M)) : Configuration M :=
  fun j => x (finSumFinEquiv (Sum.inr j))

attribute [local irreducible] graphComponent graphFormVector

end


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

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

lemma radialCut_inner_labels {L : ℕ} (y : Space) {t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (c : Fin L → Fin 2) (x : Configuration L)
    (hx : (spatialProduct (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) c).value x ≠ 0)
    (i : Fin L) (hi : ‖x i-y‖ < t) : c i ≠ 0 := by
  classical
  intro hc
  change (∏ j, (coreFirstRadialCut y ht hb (c j)).value (x j)) ≠ 0 at hx
  apply ((Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i))
  rw [hc]
  exact coreFirstRadialCut_core_zero y ht hb (x i) (by
    simpa only [radialPatchCore,mem_compl_iff,mem_ofPred_eq,not_le] using hi)

lemma radialCut_inner_count {L : ℕ} (y : Space) {a t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (hat : a ≤ t) (c : Fin L → Fin 2) (x : Configuration L)
    (hx : (spatialProduct (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) c).value x ≠ 0) :
    rawBallCount y a (cutOutPositions c x) = rawBallCount y a x := by
  classical
  rw [rawBallCount,sum_cutOutPositions c x (fun z => if ‖z-y‖ < a then 1 else 0)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : ‖x i-y‖ < a
  · rw [ite_eq_left (radialCut_inner_labels y ht hb c x hx i (hi.trans_le hat))]
  · simp only [hi,ite_false,ite_self]

theorem radial_fresh_inner_second_moment {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevVector ψ) (y : Space) {a t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (hat : a ≤ t) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      rawBallCount y a u^2*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) =
      ∫ x, rawBallCount y a x^2 ∂formRawLaw ψ := by
  dsimp only
  rw [←spatialCutExpectation_raw (coreFirstRadialCut y ht hb)
    (coreFirstRadialCut_partition y ht hb) hψ ((rawBallCount_measurable y a).pow_const 2)
    (fun x => norm_sq_le_of_nonneg (rawBallCount_nonneg y a x) (rawBallCount_le y a x))]
  unfold spatialCutExpectation
  apply Finset.sum_congr rfl
  intro c _
  rw [cutOuter_expectation_eq_full (coreFirstRadialCut y ht hb)
    (coreFirstRadialCut_partition y ht hb) hψ c ((rawBallCount_measurable y a).pow_const 2)
    (fun u => norm_sq_le_of_nonneg (rawBallCount_nonneg y a u) (rawBallCount_le y a u))]
  apply Finset.sum_congr rfl
  intro s _
  apply integral_congr_ae (ae_of_all _ _)
  intro x
  by_cases hx : (spatialProduct (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) c).value x = 0
  · simp only [multiplyForm,hx,Complex.ofReal_zero,zero_mul,norm_zero,
      zero_pow (by decide : 2 ≠ 0),mul_zero]
  · rw [radialCut_inner_count y ht hb hat c x hx]

open MeasureTheory Set Filter Metric
open scoped BigOperators ContDiff

open CoulombAnalysis CoulombNeumann

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_BindingSums
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
section Work_CurrentBindingSums_scope

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy
  graphNuclear weightedMass weightedNuclear weightedPairs

def graphNuclearSum {N : ℕ} (F : fermionGraph N) : ℝ :=
  ∑ s,∑ i,∫ x, ‖graphComponent s none F x‖^2/‖x i‖

end Work_CurrentBindingSums_scope

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy

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

lemma localOffsetMass_mono {D E : ℝ} (h : D ≤ E) (y : Space) :
    localOffsetMass D y ≤ localOffsetMass E y := by
  unfold localOffsetMass
  gcongr
  exact div_nonneg (norm_nonneg _) (by norm_num)

end CoulombAtom

end Work_UnshiftedCellCount_barrier_scope

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology

namespace CoulombBarrier
open CoulombAtom CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] masterWidth masterKernel originalRawKernel physicalObservationLaw
  originalDatum jointMasterPosterior

lemma masterKernel_amplitude {g : Space → ℝ} (hg : Continuous g)
    (hgs : tsupport g ⊆ ball 0 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {c₁ r₀ s : ℝ},
      0 < c₁ → c₁ < (10*(100000:ℝ))⁻¹ → 0 < r₀ → 0 < s → s ≤ 1 →
      ∀ x y, masterKernel c₁ r₀ s g x y ≤ A*(masterWidth c₁ r₀ s y)⁻¹^3 := by
  have hcg : HasCompactSupport g :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space) 1)
      (fun x hx => ball_subset_closedBall (hgs (subset_tsupport g hx)))
  obtain ⟨z,hz⟩ := (hg.pow 2).norm.exists_forall_ge_of_hasCompactSupport (hcg.mul_left).norm
  let B := ‖(g z)^2‖
  have hB : 0 ≤ B := norm_nonneg _
  refine ⟨8*B,by positivity,?_⟩
  intro c₁ r₀ s hc hcL hr hs hs1 x y
  rw [masterKernel_eq_widthKernel hc hr hs g]
  have he := congrFun (widthKernel_clamp (masterWidth_small_lipschitz hc hcL hr hs hs1)
    (masterWidth_pos hc hr hs) (by norm_num) (masterProfile_support hgs) y) x
  rw [he,widthKernel]
  have hp := masterWidth_pos hc hr hs y
  have hi : (max (masterWidth c₁ r₀ s x) (masterWidth c₁ r₀ s y/2))⁻¹ ≤
      (masterWidth c₁ r₀ s y/2)⁻¹ := inv_anti₀ (half_pos hp) (le_max_right _ _)
  have hgB : (g ((max (masterWidth c₁ r₀ s x) (masterWidth c₁ r₀ s y/2))⁻¹ • (y-x)))^2 ≤ B := by
    exact (le_abs_self _).trans (hz _)
  have hi0 : 0 ≤ (max (masterWidth c₁ r₀ s x) (masterWidth c₁ r₀ s y/2))⁻¹ :=
    inv_nonneg.mpr ((half_pos hp).le.trans (le_max_right _ _))
  calc
    _ ≤ (masterWidth c₁ r₀ s y/2)⁻¹^3*B :=
      mul_le_mul (pow_le_pow_left₀ hi0 hi 3) hgB (sq_nonneg _) (by positivity)
    _ = _ := by rw [inv_div]; ring

def rawAnnularCount {N : ℕ} (a b : ℝ) (x : Configuration N) : ℝ :=
  ∑ i, if a ≤ ‖x i‖ ∧ ‖x i‖ ≤ b then 1 else 0

lemma rawAnnularCount_nonneg {N : ℕ} (a b : ℝ) (x : Configuration N) :
    0 ≤ rawAnnularCount a b x := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> norm_num

lemma rawAnnularCount_le {N : ℕ} (a b : ℝ) (x : Configuration N) :
    rawAnnularCount a b x ≤ N := by
  calc
    _ ≤ ∑ _ : Fin N, (1:ℝ) := Finset.sum_le_sum fun i _ => by split_ifs <;> norm_num
    _ = N := by simp

lemma rawAnnularCount_measurable {N : ℕ} (a b : ℝ) :
    Measurable (rawAnnularCount (N := N) a b) := by
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.ite
    ((isClosed_le continuous_const (continuous_apply i).norm).inter
      (isClosed_le (continuous_apply i).norm continuous_const)).measurableSet measurable_const

end CoulombBarrier

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

 def closedAnnularShell (alpha beta : ℝ) : Set Space := {x | alpha ≤ ‖x‖ ∧ ‖x‖ ≤ beta}
lemma closedAnnularShell_compact (alpha beta : ℝ) : IsCompact (closedAnnularShell alpha beta) := by
  have he : closedAnnularShell alpha beta = closedBall (0:Space) beta ∩ {x | alpha ≤ ‖x‖} := by
    ext x
    simp only [closedAnnularShell,mem_ofPred_eq,mem_inter_iff,mem_closedBall,dist_zero_right]
    exact and_comm
  rw [he]
  exact (isCompact_closedBall (0:Space) beta).inter_right (isClosed_le continuous_const continuous_norm)

lemma exists_annularCellStencil {alpha : ℝ} (ha : 0 < alpha) (beta : ℝ) :
    ∃ T : Finset Space, (∀ v ∈ T, alpha ≤ ‖v‖ ∧ ‖v‖ ≤ beta) ∧
      ∀ x : Space, alpha ≤ ‖x‖ → ‖x‖ ≤ beta → ∃ v ∈ T, ‖x-v‖ < localCellRadius v := by
  classical
  let S := closedAnnularShell alpha beta
  have hc : S ⊆ ⋃ v : S, ball (v:Space) (localCellRadius v) := by
    intro x hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp (ha.trans_le hx.1)
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,by simpa using localCellRadius_pos hx0⟩
  obtain ⟨t,ht⟩ := (closedAnnularShell_compact alpha beta).elim_finite_subcover
    (fun v : S => ball (v:Space) (localCellRadius v)) (fun _ => isOpen_ball) hc
  refine ⟨t.image (fun v : S => (v:Space)),?_,?_⟩
  · intro v hv
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hv
    exact w.property
  · intro x hx hxb
    obtain ⟨v,hv,hxv⟩ := mem_iUnion₂.mp (ht (show x ∈ S from ⟨hx,hxb⟩))
    exact ⟨v,Finset.mem_image.mpr ⟨v,hv,rfl⟩,mem_ball_iff_norm.mp hxv⟩

lemma localCellRadius_smul {u : ℝ} (hu : 0 ≤ u) (v : Space) :
    localCellRadius (u • v) = u*localCellRadius v := by
  simp only [localCellRadius,norm_smul,Real.norm_of_nonneg hu]
  ring

lemma annularCell_scaled_cover {alpha beta u : ℝ} (hu : 0 < u)
    (T : Finset Space)
    (hC : ∀ x : Space, alpha ≤ ‖x‖ → ‖x‖ ≤ beta → ∃ v ∈ T, ‖x-v‖ < localCellRadius v)
    {x : Space} (hx : alpha*u ≤ ‖x‖) (hxb : ‖x‖ ≤ beta*u) :
    ∃ v ∈ T.image (fun v => u • v), ‖x-v‖ < localCellRadius v := by
  have hnorm : ‖u⁻¹ • x‖ = ‖x‖/u := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hu.le)]
    ring
  have hal : alpha ≤ ‖u⁻¹ • x‖ := by rw [hnorm]; exact (le_div_iff₀ hu).mpr hx
  have hbe : ‖u⁻¹ • x‖ ≤ beta := by rw [hnorm]; exact (div_le_iff₀ hu).mpr hxb
  obtain ⟨v,hv,hxv⟩ := hC (u⁻¹ • x) hal hbe
  refine ⟨u • v,Finset.mem_image.mpr ⟨v,hv,rfl⟩,?_⟩
  have hid : x-u • v = u • (u⁻¹ • x-v) := by rw [smul_sub,smul_smul,mul_inv_cancel₀ hu.ne',one_smul]
  rw [hid,norm_smul,Real.norm_of_nonneg hu.le,localCellRadius_smul hu.le]
  exact mul_lt_mul_of_pos_left hxv hu

lemma rawAnnularCount_le_cover {N : ℕ} (x : Configuration N) (a b : ℝ)
    (T : Finset Space) (r : Space → ℝ)
    (hcover : ∀ z : Space, a ≤ ‖z‖ → ‖z‖ ≤ b → ∃ v ∈ T, ‖z-v‖ < r v) :
    rawAnnularCount a b x ≤ ∑ v ∈ T, rawBallCount v (r v) x := by
  classical
  unfold rawAnnularCount rawBallCount
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  by_cases hx : a ≤ ‖x i‖ ∧ ‖x i‖ ≤ b
  · rw [ite_eq_left hx]
    obtain ⟨v,hv,hiv⟩ := hcover (x i) hx.1 hx.2
    have hh := Finset.single_le_sum (f := fun w => if ‖x i-w‖ < r w then (1:ℝ) else 0)
      (fun _ _ => by split_ifs <;> norm_num) hv
    simpa only [ite_eq_left hiv] using hh
  · rw [ite_eq_right hx]
    exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

 def rawAnnularMoment {N : ℕ} (psi : FormVector N) (a b : ℝ) : ℝ :=
    rawFormPair psi (fun x => rawAnnularCount a b x^2)

end Work_AnnularCellGeometry_barrier_scope

open MeasureTheory Set Metric

lemma localOffsetMass_annular_bound {alpha beta u D : ℝ} (ha : 0 < alpha) (hu : 0 < u)
    (hD : 0 ≤ D) {v : Space} (hv : alpha ≤ ‖v‖) (hvb : ‖v‖ ≤ beta) :
    localOffsetMass D (u • v) ≤ annularCellScaleConstant alpha beta*annularOffsetMass D u := by
  let a := localCellRadius (u • v)
  let c := (100000/alpha)^3
  let K := max c 1
  let Q := max (1/u^3) 1
  let k := Real.sqrt (beta/100000)
  have hb : 0 < beta := lt_of_lt_of_le (ha.trans_le hv) hvb
  have had : u*(alpha/100000) ≤ a := by
    dsimp [a]
    rw [localCellRadius_smul hu.le]
    unfold localCellRadius
    gcongr
  have hadp : 0 < u*(alpha/100000) := by positivity
  have hap : 0 < a := hadp.trans_le had
  have hab : a ≤ (beta/100000)*u := by
    dsimp [a]
    rw [localCellRadius_smul hu.le]
    unfold localCellRadius
    nlinarith [mul_le_mul_of_nonneg_left hvb hu.le]
  have hinv : 1/a^3 ≤ c*(1/u^3) := by
    calc _ ≤ 1/(u*(alpha/100000))^3 :=
          one_div_le_one_div_of_le (pow_pos hadp 3) (pow_le_pow_left₀ hadp.le had 3)
         _ = _ := by dsimp [c]; field_simp
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hK : 1 ≤ K := le_max_right _ _
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hQ : 1 ≤ Q := le_max_right _ _
  have hQ0 : 0 ≤ Q := le_trans zero_le_one hQ
  have hmax : max (1/a^3) 1 ≤ K*Q := by
    apply max_le
    · exact hinv.trans (mul_le_mul (le_max_left _ _) (le_max_left _ _) (by positivity) hK0)
    · exact (one_le_mul_of_one_le_of_one_le hK hQ)
  have hroot : Real.sqrt (D*a) ≤ k*Real.sqrt (D*u) := by
    have hh : D*a ≤ (beta/100000)*(D*u) := by nlinarith [mul_le_mul_of_nonneg_left hab hD]
    calc _ ≤ Real.sqrt ((beta/100000)*(D*u)) := Real.sqrt_le_sqrt hh
         _ = _ := by rw [Real.sqrt_mul (by positivity : 0 ≤ beta/100000)]
  have hcross1 : 0 ≤ K*Real.sqrt (D*u) := mul_nonneg hK0 (Real.sqrt_nonneg _)
  have hcross2 : 0 ≤ k*Q := mul_nonneg (Real.sqrt_nonneg _) hQ0
  change max (1/a^3) 1+Real.sqrt (D*a) ≤ (K+k)*(Q+Real.sqrt (D*u))
  nlinarith only [hmax,hroot,hcross1,hcross2]

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

 lemma localOffsetMass_annular_bound_norm {alpha beta u D : ℝ}
    (ha : 0 < alpha) (hu : 0 < u) (hD : 0 ≤ D) {y : Space}
    (hya : alpha*u ≤ ‖y‖) (hyb : ‖y‖ ≤ beta*u) :
    localOffsetMass D y ≤ annularCellScaleConstant alpha beta*annularOffsetMass D u := by
  have hn : ‖u⁻¹ • y‖ = ‖y‖/u := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hu.le)]; ring
  have hy1 : alpha ≤ ‖u⁻¹ • y‖ := by rw [hn]; exact (le_div_iff₀ hu).2 hya
  have hy2 : ‖u⁻¹ • y‖ ≤ beta := by rw [hn]; exact (div_le_iff₀ hu).2 hyb
  simpa only [smul_smul,mul_inv_cancel₀ hu.ne',one_smul] using
    localOffsetMass_annular_bound ha hu hD hy1 hy2

 lemma localOffsetMass_annular_cost {alpha beta u D : ℝ}
    (ha : 0 < alpha) (hu : 0 < u) (hD : 0 ≤ D) {y : Space}
    (hya : alpha*u ≤ ‖y‖) (hyb : ‖y‖ ≤ beta*u) :
    (localOffsetMass D y)^2/localCellRadius y ≤
      annularCellCostConstant alpha beta*(annularOffsetMass D u)^2/u := by
  have hyp : 0 < ‖y‖ := (mul_pos ha hu).trans_le hya
  have hr : 0 < localCellRadius y := localCellRadius_pos (norm_pos_iff.mp hyp)
  have hrad : alpha*u/100000 ≤ localCellRadius y := by
    unfold localCellRadius
    linarith
  have hn := localOffsetMass_annular_bound_norm ha hu hD hya hyb
  calc
    _ ≤ (annularCellScaleConstant alpha beta*annularOffsetMass D u)^2/localCellRadius y :=
      div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (zero_le_one.trans (localOffsetMass_one_le D y)) hn 2) hr.le
    _ ≤ (annularCellScaleConstant alpha beta*annularOffsetMass D u)^2/(alpha*u/100000) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hrad
    _ = _ := by unfold annularCellCostConstant; field_simp

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

lemma annularInnerRadiusScale {D h : ℝ} (hD : 0 ≤ D) (hh : 0 < h)
    {z : Space} (hz : z ∈ innerFieldTestAnnulus h) :
    (localOffsetMass D z/localCellRadius z)^2 ≤
      3*(annularCellScaleConstant 1 3*100000)^2*innerScale D h := by
  have hn := localOffsetMass_annular_bound_norm (alpha := 1) (beta := 3)
    (by norm_num) hh hD (by simpa only [one_mul] using hz.1) hz.2
  have ha : 0 < localCellRadius z := localCellRadius_pos (norm_pos_iff.mp (hh.trans_le hz.1))
  have har : h/100000 ≤ localCellRadius z := by unfold localCellRadius; linarith [hz.1]
  have hc := annularCellScaleConstant_one_le (1:ℝ) 3
  have hs := annularOffsetMass_one_le D h
  calc
    _ ≤ ((annularCellScaleConstant 1 3*annularOffsetMass D h)/(h/100000))^2 := by
      apply pow_le_pow_left₀ (div_nonneg (zero_le_one.trans (localOffsetMass_one_le D z)) ha.le)
      exact (div_le_div_of_nonneg_right hn ha.le).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity) har)
    _ = (annularCellScaleConstant 1 3*100000)^2*((annularOffsetMass D h)^2/h^2) := by ring
    _ ≤ (annularCellScaleConstant 1 3*100000)^2*(3*innerScale D h) :=
      mul_le_mul_of_nonneg_left (annularOffsetMass_sq_div hD hh) (sq_nonneg _)
    _ = _ := by ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_BarrierEventSymmetryBarrier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set

namespace CoulombAtom
open CoulombObservation

def arrayObservedConfiguration {N K : ℕ} (k : Fin K)
    (u : Fin K × (Fin N × Fin 3) → ℝ) : Configuration N :=
  fun i => WithLp.toLp 2 (fun a => u (k,i,a))

def arrayUnorderedConfiguration {N K : ℕ} (k : Fin K)
    (u : Fin K × (Fin N × Fin 3) → ℝ) : UnorderedConfiguration N :=
  unorderedConfiguration (arrayObservedConfiguration k u)

@[instance_reducible] def arrayObservationInformation (N K j : ℕ) :
    MeasurableSpace (Fin K × (Fin N × Fin 3) → ℝ) :=
  ⨆ k : Fin K, if j ≤ k.val then
    MeasurableSpace.comap (arrayUnorderedConfiguration (N := N) k) inferInstance else ⊥

@[instance_reducible] def symmetricArraySpace (N K : ℕ) : MeasurableSpace (Fin K × (Fin N × Fin 3) → ℝ) where
  MeasurableSet' := QuantumEventSymmetric
  measurableSet_empty := fun _ _ => Iff.rfl
  measurableSet_compl := fun _ h π u => not_congr (h π u)
  measurableSet_iUnion := by
    intro f h π u
    simp only [mem_iUnion]
    exact exists_congr (fun n => h n π u)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_Observation
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Set

lemma exists_scaled_shell_stencil :
    ∃ L : ℕ, ∀ u : ℝ, 0 < u → ∃ ys : List Space,
      ys.length = L ∧ (∀ y ∈ ys, u/2 ≤ ‖y‖ ∧ ‖y‖ ≤ 4*u) ∧
      ∀ z : Space, u/2 ≤ ‖z‖ → ‖z‖ ≤ 4*u → ∃ y ∈ ys, ‖z-y‖ < localCellRadius y := by
  classical
  obtain ⟨T,hT,hcover⟩ := exists_annularCellStencil (by norm_num : (0:ℝ)<1/2) 4
  refine ⟨T.card,fun u hu => ⟨(T.toList.map (fun v => u • v)),by simp,?_,?_⟩⟩
  · intro y hy
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hy
    have hvT := hT v (Finset.mem_toList.mp hv)
    rw [norm_smul,Real.norm_of_nonneg hu.le]
    constructor <;> nlinarith [hvT.1,hvT.2]
  · intro z hz hz4
    obtain ⟨y,hy,hd⟩ := annularCell_scaled_cover hu T hcover (by linarith) hz4
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    exact ⟨u • v,List.mem_map.mpr ⟨v,Finset.mem_toList.mpr hv,rfl⟩,hd⟩

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_UniformEventGraph
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace NNReal

namespace CoulombAtom
open CoulombObservation

attribute [local irreducible] graphComponent graphFormVector
  FermionLipschitzMultiplier.apply coulombFormOperator fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator

def observationGraphFactor (N : ℕ) {J : Type*} [Fintype J] (b : J → ℝ) (p₀ : ℝ) : ℝ :=
  3*((Real.sqrt p₀)⁻¹)^2 + 2*(∑ i : Fin N, ∑ a : Fin 3,
    ((Real.sqrt p₀)⁻¹ *
      ((sqrtLikelihoodLipschitzConstant (I := Fin N × Fin 3) b : ℝ) *
        ‖flattenConfiguration N‖) * ‖direction i a‖)^2)

attribute [local irreducible] quantumEventMultiplier

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierSpatialNetBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierSpatialNet_barrier_scope

open Set Metric
open scoped BigOperators

open CoulombAtom

def spatialGridIndex (h : ℝ) (x : Space) : Fin 3 → ℤ := fun i => ⌊x i / h⌋

end Work_BarrierSpatialNet_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

open CoulombAtom CoulombAnalysis CoulombObservation

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SharpFreshPatchBarrier
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
open scoped BigOperators InnerProductSpace

namespace CoulombAtom

 def smoothMultiplyL2 (p : SmoothMultiplier spaceDirections)
    (f : Lp ℂ 2 (volume : Measure Space)) : Lp ℂ 2 (volume : Measure Space) :=
  (memLp_bounded_mul p.regular.continuous p.bound (Lp.memLp f)).toLp _

 def smoothDerivativeProductL2 (p : SmoothMultiplier spaceDirections)
    (a : Fin 3) (f g : Lp ℂ 2 (volume : Measure Space)) : Lp ℂ 2 (volume : Measure Space) :=
  ((memLp_bounded_mul p.regular.continuous p.bound (Lp.memLp g)).add
    (memLp_bounded_mul (p.derivative_continuous a) (p.gradient_bound a) (Lp.memLp f))).toLp _

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_LocalOrdinaryBarrier
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
section Work_LocalOrdinaryLT_barrier_scope

open MeasureTheory Filter
open scoped BigOperators ENNReal

open CoulombPauli CoulombPackets CoulombLT

 def densityLocalizationError {N : ℕ} (ψ : FormVector N)
    (p : SmoothMultiplier spaceDirections) : ℝ :=
  ∑ a : Fin 3, weightedParticleCount ψ
    (fun x => (lineDeriv ℝ p.value x (spaceDirections a))^2)

 def localDensityBudget {N : ℕ} (ψ : FormVector N)
    (p : SmoothMultiplier spaceDirections) : ℝ :=
  32*weightedParticleCount ψ (fun x => p.value x^2)+
    (4096/3:ℝ)*(localGradientTrace ψ p+densityLocalizationError ψ p)

end Work_LocalOrdinaryLT_barrier_scope

open MeasureTheory Filter Set
open scoped BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ObservedAnnularCountBarrier
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

def observedAnnularCount {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K) (a b : ℝ)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) : ℝ :=
  rawAnnularCount a b (physicalObservedConfiguration ell k z)

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
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PosteriorFreshTestBarrier
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
open scoped BigOperators NNReal ENNReal

namespace CoulombAtom
open CoulombObservation CoulombNeumann CoulombAnalysis

def freshRadialTest {N : ℕ} (y : Space) (t : ℝ) {b : ℝ} (hb : 0 < b)
    (g : Space → ℝ) (c : Fin N → Fin 2) (s : Spins (cutOutNumber c))
    (u : Configuration (cutOutNumber c)) : ℝ :=
  ∫ z, g (y+z)*retainedPatchLp hb (radialPatchRetention N y t b c s u) u y (t-4*b) z
    ∂ballMeasure (t-4*b)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SpatialCapSubmeanBarrier
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

open MeasureTheory Set Metric

open CoulombAnalysis

def capBandStatistic (u C : ℝ) (f : Space → ℝ) : ℝ :=
  (1/((u/8)^3*(Real.pi*4/3)))*
    ∫ x in closedAnnularShell u (2*u), max ((u/100000)^4*f x-C) 0

open MeasureTheory Set Metric

open CoulombAnalysis

end CoulombAtom

end

end OAI
end


