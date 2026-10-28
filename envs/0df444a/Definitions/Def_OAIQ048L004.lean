-- Prove2me | Definitions.Def_OAIQ048L004
-- name    : OAIQ048L004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:29:08.206589+00:00
-- url     : https://prove2.me/theorems/994afa66-40fc-4bfa-a76d-1cbff8ea99fd
-- title:
--   Definitions bundle OAIQ048L004 of the split of OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LogConcaveSampling.exact_source_main`, carved from OpenAI's openai/math development (OpenAI, *Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)*, OpenAI Math Release, September 26, 2026, result family 139, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 150 declarations of OpenAI's Lean: 55 definitions, 1 inductive type or structure, 1 instance and 93 theorems. The definitions and types are `OAI.LogConcaveSampling.TensorAtom.slice`, `OAI.LogConcaveSampling.TensorAtom.spatialBound`, `OAI.LogConcaveSampling.TensorEnergy.SmoothTensorCurve`, `OAI.LogConcaveSampling.TensorEnergy.flowCorrectionMajorant`, `OAI.LogConcaveSampling.TensorEnergy.flowJetMajorant`, `OAI.LogConcaveSampling.TensorSum.HasMaterial`, `OAI.LogConcaveSampling.TensorSum.material`, `OAI.LogConcaveSampling.TensorSum.matrixEval`, `OAI.LogConcaveSampling.TensorSum.outer`, `OAI.LogConcaveSampling.TensorSum.slice`, `OAI.LogConcaveSampling.TensorSum.spatialBound`, `OAI.LogConcaveSampling.TensorSum.terminalQ`, `OAI.LogConcaveSampling.adjointCommutator`, `OAI.LogConcaveSampling.centerInitialEnvelope`, `OAI.LogConcaveSampling.centerMeanEnvelope`, `OAI.LogConcaveSampling.centerStateEnvelope`, `OAI.LogConcaveSampling.centerStateQuadratureEnvelope`, `OAI.LogConcaveSampling.centeringCalibrationGood`, `OAI.LogConcaveSampling.centeringInitialBudget`, `OAI.LogConcaveSampling.centeringMeanBudget`, `OAI.LogConcaveSampling.centeringMeanQuadratureBudget`, `OAI.LogConcaveSampling.centeringPicardBudget`, `OAI.LogConcaveSampling.centeringRowBudget`, `OAI.LogConcaveSampling.centeringStateBudget`, `OAI.LogConcaveSampling.centeringStateQuadratureBudget`, `OAI.LogConcaveSampling.composedJetMajorant`, `OAI.LogConcaveSampling.extendedSpatial`, `OAI.LogConcaveSampling.finiteRejectionAlgorithm`, `OAI.LogConcaveSampling.gaussianShiftRatio`, `OAI.LogConcaveSampling.halvingKernel`, `OAI.LogConcaveSampling.harmonicCorrectionBudget`, `OAI.LogConcaveSampling.jacobianMajorant`, `OAI.LogConcaveSampling.kernelActionNormalizedBudget`, `OAI.LogConcaveSampling.kernelActionRmsBudget`, `OAI.LogConcaveSampling.kernelAnalyticBudget`, `OAI.LogConcaveSampling.kernelAnalyticNormalizedBudget`, `OAI.LogConcaveSampling.kernelMajorant`, `OAI.LogConcaveSampling.meanCellResidual`, `OAI.LogConcaveSampling.meanMaterialVector`, `OAI.LogConcaveSampling.meanPathJet` and 16 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `LogConcave_Analysis_AffinePotential`, `LogConcave_Complexity_CenteringStateBudget`, `LogConcave_Complexity_HarmonicCorrectionBudget`, `LogConcave_Complexity_KernelActionNormalizedBudget`, `LogConcave_Complexity_KernelActionRmsBudget`, `LogConcave_Complexity_KernelAnalyticBudget`, `LogConcave_Complexity_KernelAnalyticNormalizedBudget`, `LogConcave_Complexity_SingleCellBasisBudget`, `LogConcave_Complexity_TerminalDerivativeBudget`, `LogConcave_Dynamics_StationaryPath`, `LogConcave_JetEstimates_ArrayMatrix`, `LogConcave_JetEstimates_ContractLeftSplit`, `LogConcave_JetEstimates_FlowJetMajorant`, `LogConcave_JetEstimates_ForestTensor`, `LogConcave_JetEstimates_GadjScalar`, `LogConcave_JetEstimates_JetMaterial`, `LogConcave_JetEstimates_JetRightSlice`, `LogConcave_JetEstimates_MatrixArray`, `LogConcave_JetEstimates_Reindex`, `LogConcave_JetEstimates_Slice`, `LogConcave_JetEstimates_SmoothTensorCurve`, `LogConcave_JetEstimates_SplitBundle`, `LogConcave_JetEstimates_SplitIndex`, `LogConcave_JetEstimates_Squared`, `LogConcave_LowerBounds_TranscriptRejection`, `LogConcave_Numerics_CenteringStateQuadratureBudget`, `LogConcave_OraclePrograms_CenteringMeanCircuit`, `LogConcave_Sampling_AnalyticBase`, `LogConcave_Sampling_ComposedJetMajorant`, `LogConcave_Sampling_ConditionalSlotEmbedding`, `LogConcave_Sampling_CoordinateRank`, `LogConcave_Sampling_DirectionalBasisSum`, `LogConcave_Sampling_HarmonicStationaryMoment`, `LogConcave_Sampling_JointU`, `LogConcave_Sampling_MeanMaterialVector`, `LogConcave_Sampling_NoiseKernel`, `LogConcave_Sampling_NormalizedScoreMajorant`, `LogConcave_Sampling_NormalizedTensor`, `LogConcave_Sampling_NormalizedTensorMajorantScale`, `LogConcave_Sampling_NumericalScalars`, `LogConcave_Sampling_PairGauge`, `LogConcave_Sampling_PrependTape`, `LogConcave_Sampling_ScaledMeanJet`, `LogConcave_Sampling_ScoreAugmented`, `LogConcave_Sampling_ScoreSlots`, `LogConcave_Sampling_SpatialTensorContinuous`, `LogConcave_Sampling_SpatialTransport`, `LogConcave_Sampling_TerminalBackward`, `LogConcave_Sampling_TerminalMean`, `LogConcave_Sampling_TransportCorrectionMajorant`, `LogConcave_Sampling_TransportMajorant`.
--
--   **Imports.** It imports the published bundle `Def_LogConcaveQuery`; the bundles `OAIQ048L002` and `OAIQ048L003` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanCompiled_scaled`, `OAI.LogConcaveSampling.TensorSum.matrix_one_energy`, `OAI.LogConcaveSampling.TensorSum.matrix_zero_energy`, `OAI.LogConcaveSampling.TensorSum.spatialBound_Lp`, `OAI.LogConcaveSampling.centeringMeanCircuit_rms`, `OAI.LogConcaveSampling.centeringPicard_state_rms`, `OAI.LogConcaveSampling.centeringVelocityJoint_full_rms`, `OAI.LogConcaveSampling.centering_velocity_taylor_uniform`, `OAI.LogConcaveSampling.kernelActionPicard_rms`, `OAI.LogConcaveSampling.kernelQuadraturePicard_full_rms` and `OAI.LogConcaveSampling.stationary_lie_taylor_rms`; the proofs of `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanCompiled_scaled`, `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanFrom_correct`, `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.sampleFrom_squared`, `OAI.LogConcaveSampling.OracleCompiler.exists_source_numerical_ready`, `OAI.LogConcaveSampling.TensorSum.matrix_one_energy`, `OAI.LogConcaveSampling.TensorSum.matrix_zero_energy`, `OAI.LogConcaveSampling.TensorSum.spatialBound_Lp`, `OAI.LogConcaveSampling.centeringMeanCircuit_rms`, `OAI.LogConcaveSampling.centeringPicard_state_rms`, `OAI.LogConcaveSampling.centeringTrueVelocity_continuous`, `OAI.LogConcaveSampling.centeringVelocityJoint_full_rms`, `OAI.LogConcaveSampling.centering_velocity_taylor_uniform`, `OAI.LogConcaveSampling.eventually_subpolynomial_sampler`, `OAI.LogConcaveSampling.exact_source_main`, `OAI.LogConcaveSampling.exists_centering_stationaryPath`, `OAI.LogConcaveSampling.kernelActionPicard_rms`, `OAI.LogConcaveSampling.kernelCorrectionPicard_rms`, `OAI.LogConcaveSampling.kernelQuadraturePicard_full_rms`, `OAI.LogConcaveSampling.probabilityAnchored_marginal_rms`, `OAI.LogConcaveSampling.sampleMeanCircuit_rms`, `OAI.LogConcaveSampling.stationaryMeanTarget_identity` and `OAI.LogConcaveSampling.stationary_lie_taylor_rms`.
-- source:
--   OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 139; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L002
import Definitions.Def_OAIQ048L003

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_AffinePotential
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

variable {d : ℕ}

def gaussianShiftRatio (a z : Point d) : ℝ :=
  Real.exp (inner ℝ a z-‖a‖^2/2)

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ConditionalSlotEmbedding
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

theorem conditional_jet_cumulant_energy {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2 ≤ 1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d)
    {ι ϑ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ϑ] [DecidableEq ϑ]
    (s : ι → Bool) (t : ϑ → Bool) (l : List ι) (k : List ϑ)
    (hlN : l.Nodup) (hlall : l.toFinset=Finset.univ)
    (hkN : k.Nodup) (hkall : k.toFinset=Finset.univ) (hlne : l≠[]) (hkne : k≠[])
    (o : List (ι ⊕ ϑ)) (ho : o.Perm (l.map Sum.inl++k.map Sum.inr)) :
    let μ := jointConditionalLaw F x r ρ y ((lam:ℝ)*r)
    let b := EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ
    TensorEnergy.Bound (fun (a : ι → Fin d) (c : ϑ → Fin d) =>
      JetCalculus.jet (Sum.elim (fun i => b (conditionalSlotEmbedding d s a i))
        (fun j => b (conditionalSlotEmbedding d t c j))) o
        (fun z => Real.log (Appell.laplace μ (fun _ => (1:ℝ)) z)) 0)
      (((Fintype.card ι+Fintype.card ϑ+1:ℕ):ℝ)^(2*(Fintype.card ι+Fintype.card ϑ+1)) *
        Appell.splitConstant (2*Real.pi^2*(1-ρ^2)) (Fintype.card ι) (Fintype.card ϑ)) := by
  obtain ⟨hp,hm,hP⟩ := jointConditionalLaw_properties hF x hr hlam hl hρ0 hρ1 y
  let := hp
  have hβ : 0 ≤ 2*Real.pi^2*(1-ρ^2) := by
    obtain ⟨ha,_⟩ := probability_time hρ0 hρ1
    positivity
  exact (Appell.actual_jet_cumulant_energy hm hβ hP
      (EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ) l k hlN hlall hkN hkall hlne hkne o ho).submatrix
    (conditionalSlotEmbedding d s) (conditionalSlotEmbedding d t)

theorem conditional_normalized_tensor_energy {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2 ≤ 1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d)
    {ι ϑ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ϑ] [DecidableEq ϑ]
    (s : ι → Bool) (t : ϑ → Bool) (l : List ι) (k : List ϑ)
    (hlN : l.Nodup) (hlall : l.toFinset=Finset.univ)
    (hkN : k.Nodup) (hkall : k.toFinset=Finset.univ) (hlne : l≠[]) (hkne : k≠[])
    (o : List (ι ⊕ ϑ)) (ho : o.Perm (l.map Sum.inl++k.map Sum.inr)) :
    let μ := jointConditionalLaw F x r ρ y ((lam:ℝ)*r)
    let b := EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ
    let n := Fintype.card ι+Fintype.card ϑ
    TensorEnergy.Bound (fun (a : ι → Fin d) (c : ϑ → Fin d) =>
      ((1-ρ^2)^(n-1))⁻¹ * JetCalculus.jet (Sum.elim (fun i => b (conditionalSlotEmbedding d s a i))
        (fun j => b (conditionalSlotEmbedding d t c j))) o
        (fun z => Real.log (Appell.laplace μ (fun _ => (1:ℝ)) z)) 0)
      (((n+1:ℕ):ℝ)^(2*(n+1))*(2*Real.pi^2)^n *
        (((Fintype.card ι).factorial:ℝ)*((Fintype.card ϑ).factorial:ℝ))^2 /
          (1-ρ^2)^(n-2)) := by
  dsimp only
  have hj : 0<Fintype.card ι := by
    apply Fintype.card_pos_iff.mpr
    obtain ⟨i,_⟩ := List.exists_mem_of_ne_nil l hlne
    exact ⟨i⟩
  have hk : 0<Fintype.card ϑ := by
    apply Fintype.card_pos_iff.mpr
    obtain ⟨i,_⟩ := List.exists_mem_of_ne_nil k hkne
    exact ⟨i⟩
  have hb := (conditional_jet_cumulant_energy hF x hr hlam hl hρ0 hρ1 y
    s t l k hlN hlall hkN hkall hlne hkne o ho).smul
      (((1-ρ^2)^(Fintype.card ι+Fintype.card ϑ-1))⁻¹)
  convert! hb using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [Appell.splitConstant]
  have he := normalized_energy_factor (probability_time hρ0 hρ1).1.ne' (2*Real.pi^2) hj hk
  calc
    _ = (((Fintype.card ι+Fintype.card ϑ+1:ℕ):ℝ)^(2*(Fintype.card ι+Fintype.card ϑ+1)) *
      (((Fintype.card ι).factorial:ℝ)*((Fintype.card ϑ).factorial:ℝ))^2) *
      ((2*Real.pi^2)^(Fintype.card ι+Fintype.card ϑ)/(1-ρ^2)^(Fintype.card ι+Fintype.card ϑ-2)) := by ring
    _ = _ := by rw [←he]; ring

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.TensorEnergy
open scoped Classical

universe u
variable {S R : Type u} [Fintype S] [Fintype R] {d : ℕ}

lemma AllSplitBound.reindex {T : (S → Fin d) → ℝ} {M : ℝ}
    (hT : AllSplitBound T M) (e : S ≃ R) :
    AllSplitBound (fun a : R → Fin d => T (a ∘ e)) M := by
  intro I O _ _ _ _ _ _ f
  exact hT I O (e.trans f)

end LogConcaveSampling.TensorEnergy

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_ContractLeftSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators

universe u
variable {Ai Ao Bi Bo : Type u} [Fintype Ai] [Fintype Ao] [Fintype Bi] [Fintype Bo] {d : ℕ}

lemma allSplit_contract_oriented [Nonempty Ao] [Nonempty Bi]
    {A : ((Ai ⊕ Ao) ⊕ Unit → Fin d) → ℝ}
    {B : ((Bi ⊕ Bo) ⊕ Unit → Fin d) → ℝ} {M N : ℝ}
    (hA : AllSplitBound A M) (hB : AllSplitBound B N) :
    Bound (fun (o : (Ao → Fin d) × (Bo → Fin d)) (i : (Ai → Fin d) × (Bi → Fin d)) =>
      ∑z : Fin d,A (Sum.elim (Sum.elim i.1 o.1) (fun _ => z))*
        B (Sum.elim (Sum.elim i.2 o.2) (fun _ => z))) ((M*N)^2) := by
  have ha := (hA (Ai ⊕ Unit) Ao contractLeftSplit).reindex
    (Equiv.refl (Ao → Fin d)) (appendCoordinate Ai)
  have hb := (hB Bi (Unit ⊕ Bo) contractRightSplit).reindex
    (prependCoordinate Bo) (Equiv.refl (Bi → Fin d))
  have hab := ha.contract hb (sq_nonneg M)
  convert hab using 1
  · funext o i
    apply Finset.sum_congr rfl
    intro z hz
    congr 1
    · congr 1
      funext s
      rcases s with (s|s)|s <;> rfl
    · congr 1
      funext s
      rcases s with (s|s)|s <;> rfl
  · ring

lemma allSplit_contract_reverse [Nonempty Ai] [Nonempty Bo]
    {A : ((Ai ⊕ Ao) ⊕ Unit → Fin d) → ℝ}
    {B : ((Bi ⊕ Bo) ⊕ Unit → Fin d) → ℝ} {M N : ℝ}
    (hA : AllSplitBound A M) (hB : AllSplitBound B N) :
    Bound (fun (o : (Ao → Fin d) × (Bo → Fin d)) (i : (Ai → Fin d) × (Bi → Fin d)) =>
      ∑z : Fin d,A (Sum.elim (Sum.elim i.1 o.1) (fun _ => z))*
        B (Sum.elim (Sum.elim i.2 o.2) (fun _ => z))) ((M*N)^2) := by
  have h := (allSplit_contract_oriented hB hA).reindex
    (Equiv.prodComm (Ao → Fin d) (Bo → Fin d))
    (Equiv.prodComm (Ai → Fin d) (Bi → Fin d))
  simpa only [Equiv.prodComm_apply,Prod.swap_prod_mk,Prod.fst_swap,Prod.snd_swap,mul_comm] using h

lemma allSplit_contract_either
    {A : ((Ai ⊕ Ao) ⊕ Unit → Fin d) → ℝ}
    {B : ((Bi ⊕ Bo) ⊕ Unit → Fin d) → ℝ} {M N : ℝ}
    (hA : AllSplitBound A M) (hB : AllSplitBound B N)
    (ho : (Nonempty Ao ∧ Nonempty Bi) ∨ (Nonempty Ai ∧ Nonempty Bo)) :
    Bound (fun (o : (Ao → Fin d) × (Bo → Fin d)) (i : (Ai → Fin d) × (Bi → Fin d)) =>
      ∑z : Fin d,A (Sum.elim (Sum.elim i.1 o.1) (fun _ => z))*
        B (Sum.elim (Sum.elim i.2 o.2) (fun _ => z))) ((M*N)^2) := by
  rcases ho with ⟨_,_⟩|⟨_,_⟩
  · exact allSplit_contract_oriented hA hB
  · exact allSplit_contract_reverse hA hB

section partition
variable {S T : Type u} [Fintype S] [Fintype T]

attribute [local instance] OAI.LogConcaveSampling.TensorEnergy.leftInDec
attribute [local instance] OAI.LogConcaveSampling.TensorEnergy.leftOutDec
attribute [local instance] OAI.LogConcaveSampling.TensorEnergy.rightInDec
attribute [local instance] OAI.LogConcaveSampling.TensorEnergy.rightOutDec
lemma singleContract_split_bound [Nonempty S] [Nonempty T]
    {A : (S ⊕ Unit → Fin d) → ℝ} {B : (T ⊕ Unit → Fin d) → ℝ}
    {M N : ℝ} (hA : AllSplitBound A M) (hB : AllSplitBound B N)
    (p : ProperSplit (S ⊕ T)) :
    Bound (splitMatrix (singleContract A B) p) ((M*N)^2) := by
  let eS := partEquiv (fun s : S => p.val (Sum.inl s))
  let eT := partEquiv (fun t : T => p.val (Sum.inr t))
  have ha := hA.reindex (eS.sumCongr (Equiv.refl Unit))
  have hb := hB.reindex (eT.sumCongr (Equiv.refl Unit))
  have h : Bound (fun (o : ({s : S // ¬p.val (Sum.inl s)=true} → Fin d) ×
            ({t : T // ¬p.val (Sum.inr t)=true} → Fin d))
        (i : ({s : S // p.val (Sum.inl s)=true} → Fin d) ×
            ({t : T // p.val (Sum.inr t)=true} → Fin d)) =>
      ∑z : Fin d,A ((Sum.elim (Sum.elim i.1 o.1) (fun _ => z)) ∘ eS.sumCongr (Equiv.refl Unit))*
        B ((Sum.elim (Sum.elim i.2 o.2) (fun _ => z)) ∘ eT.sumCongr (Equiv.refl Unit)))
        ((M*N)^2) := by
    exact allSplit_contract_either
      (Ai:={s : S // p.val (Sum.inl s)=true})
      (Ao:={s : S // ¬p.val (Sum.inl s)=true})
      (Bi:={t : T // p.val (Sum.inr t)=true})
      (Bo:={t : T // ¬p.val (Sum.inr t)=true})
      (A:=fun f => A (f ∘ eS.sumCongr (Equiv.refl Unit)))
      (B:=fun f => B (f ∘ eT.sumCongr (Equiv.refl Unit))) ha hb (splitOrientation p)
  have hh := h.reindex (outputCoords p) (inputCoords p)
  suffices he : splitMatrix (singleContract A B) p =
      (fun o i => ∑z : Fin d,
        A ((Sum.elim (Sum.elim (inputCoords p i).1 (outputCoords p o).1) (fun _ => z)) ∘
          eS.sumCongr (Equiv.refl Unit))*
        B ((Sum.elim (Sum.elim (inputCoords p i).2 (outputCoords p o).2) (fun _ => z)) ∘
          eT.sumCongr (Equiv.refl Unit))) by
    rw [he]
    exact hh
  ext o i
  unfold splitMatrix singleContract
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  · congr 1
    funext s
    rcases s with s|s
    · exact (part_colors_left p o i s).symm
    · rfl
  · congr 1
    funext t
    rcases t with t|t
    · exact (part_colors_right p o i t).symm
    · rfl

end partition

end LogConcaveSampling.TensorEnergy

namespace LogConcaveSampling.TensorEnergy
open scoped Classical

universe u

lemma allSplitBound_of_proper {S : Type u} [Fintype S] {d : ℕ}
    {T : (S → Fin d) → ℝ} {M : ℝ}
    (h : ∀p : ProperSplit S,Bound (splitMatrix T p) (M^2)) : AllSplitBound T M := by
  intro I O _ _ _ _ _ _ e
  have h' := (h (properOfEquiv e)).reindex
    (Equiv.arrowCongr (rightOfEquiv e) (Equiv.refl (Fin d)))
    (Equiv.arrowCongr (leftOfEquiv e) (Equiv.refl (Fin d)))
  convert h' using 1
  all_goals try with_reducible_and_instances rfl
  ext o i
  unfold splitMatrix
  congr 1
  funext s
  rw [splitEquiv_ofEquiv]
  cases e s <;> simp

lemma AllSplitBound.singleContract {S T : Type u} [Fintype S] [Fintype T]
    [Nonempty S] [Nonempty T] {d : ℕ}
    {A : (S ⊕ Unit → Fin d) → ℝ} {B : (T ⊕ Unit → Fin d) → ℝ}
    {M N : ℝ} (hA : AllSplitBound A M) (hB : AllSplitBound B N) :
    AllSplitBound (singleContract A B) (M*N) :=
  allSplitBound_of_proper (singleContract_split_bound hA hB)

end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators Matrix.Norms.L2Operator

universe u
variable {S : Type u} [Fintype S] {d : ℕ}

lemma AllSplitBound.mono {T : (S → Fin d) → ℝ} {M N : ℝ}
    (h : AllSplitBound T M) (hM : 0≤M) (hMN : M≤N) : AllSplitBound T N := by
  intro I O _ _ _ _ _ _ e
  exact (h I O e).mono (pow_le_pow_left₀ hM hMN 2)

lemma AllSplitBound.const_mul {T : (S → Fin d) → ℝ} {M : ℝ}
    (h : AllSplitBound T M) (c : ℝ) : AllSplitBound (fun a => c*T a) (c*M) := by
  intro I O _ _ _ _ _ _ e
  convert (h I O e).smul c using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma AllSplitBound.finite_sum {J : Type*} [Fintype J]
    {T : J → (S → Fin d) → ℝ} {M : J → ℝ}
    (hM : ∀j,0≤M j) (h : ∀j,AllSplitBound (T j) (M j)) :
    AllSplitBound (fun a => ∑j,T j a) (∑j,M j) := by
  intro I O _ _ _ _ _ _ e
  exact Bound.finite_sum_norm hM (fun j => h j I O e)

lemma AllSplitBound.entry_le {T : (S → Fin d) → ℝ} {M : ℝ}
    (h : AllSplitBound T M) (hM : 0≤M) (hS : 2≤Fintype.card S) (c : S → Fin d) :
    |T c|≤M := by
  obtain ⟨p⟩ := nonempty_properSplit hS
  have hh := (h _ _ (splitEquiv p)).entry_sq
    (fun o => c ((splitEquiv p).symm (Sum.inr o)))
    (fun i => c ((splitEquiv p).symm (Sum.inl i)))
  have he : (fun s => Sum.elim (fun i => c ((splitEquiv p).symm (Sum.inl i)))
      (fun o => c ((splitEquiv p).symm (Sum.inr o))) (splitEquiv p s))=c := by
    funext s
    have hs := (splitEquiv p).symm_apply_apply s
    cases hsp : splitEquiv p s <;> simp only [Sum.elim_inl,Sum.elim_inr] <;>
      simp only [hsp] at hs <;> rw [hs]
  rw [he] at hh
  exact (sq_le_sq₀ (abs_nonneg _) hM).mp (by simpa only [sq_abs] using hh)

end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_NormalizedTensor
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators RealInnerProductSpace NNReal

universe u

lemma normalizedTensor_allSplit {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (y : Point d) {S : Type u} [Fintype S] (mask : S → Bool) (l : List S)
    (hlN : l.Nodup) (hlall : ∀s,s∈l) :
    TensorEnergy.AllSplitBound (normalizedTensor F x r ρ ((lam:ℝ)*r) y mask l)
      (normalizedTensorMajorant (Fintype.card S) (1-ρ^2)) := by
  intro I O _ _ _ _ _ _ e
  let f : S ≃ O ⊕ I := e.trans (Equiv.sumComm I O)
  let lo : List O := Finset.univ.toList
  let li : List I := Finset.univ.toList
  have hlo : lo≠[] := by
    intro h
    obtain ⟨o⟩ := ‹Nonempty O›
    have : o∈lo := by simp [lo]
    simp [h] at this
  have hli : li≠[] := by
    intro h
    obtain ⟨i⟩ := ‹Nonempty I›
    have : i∈li := by simp [li]
    simp [h] at this
  have h := conditional_normalized_tensor_energy hF x hr hlam hl hρ0 hρ1 y
    (fun o => mask (f.symm (Sum.inl o))) (fun i => mask (f.symm (Sum.inr i))) lo li
    (Finset.nodup_toList _) (by simp [lo]) (Finset.nodup_toList _) (by simp [li]) hlo hli
    (l.map f) (list_split_perm l hlN hlall f)
  have hc : Fintype.card S=Fintype.card O+Fintype.card I := by
    simpa using Fintype.card_congr f
  have ha : 0<1-ρ^2 := (probability_time hρ0 hρ1).1
  have hbound :
      (((Fintype.card O+Fintype.card I+1:ℕ):ℝ)^(2*(Fintype.card O+Fintype.card I+1)) *
        (2*Real.pi^2)^(Fintype.card O+Fintype.card I) *
        (((Fintype.card O).factorial:ℝ)*((Fintype.card I).factorial:ℝ))^2 /
        (1-ρ^2)^(Fintype.card O+Fintype.card I-2)) ≤
        (normalizedTensorMajorant (Fintype.card S) (1-ρ^2))^2 := by
    dsimp only [normalizedTensorMajorant]
    rw [Real.sq_sqrt (by positivity),hc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    rw [pow_two]
    apply mul_le_mul
    · exact_mod_cast Nat.factorial_le (Nat.le_add_right (Fintype.card O) (Fintype.card I))
    · exact_mod_cast Nat.factorial_le (Nat.le_add_left (Fintype.card I) (Fintype.card O))
    · positivity
    · positivity
  have hh := h.mono hbound
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext o i
  dsimp only [normalizedTensor]
  rw [hc,JetCalculus.jet_map]
  congr 2
  funext s
  have hs := f.symm_apply_apply s
  cases he : f s with
  | inl z =>
    have hse : s=f.symm (Sum.inl z) := by rw [←he,hs]
    subst s
    simp [f,conditionalSlotEmbedding,Function.comp_def]
    congr 1
    change (if mask _ then Sum.inr _ else Sum.inl _) = _
    simp
  | inr z =>
    have hse : s=f.symm (Sum.inr z) := by rw [←he,hs]
    subst s
    simp [f,conditionalSlotEmbedding,Function.comp_def]
    congr 1
    change (if mask _ then Sum.inr _ else Sum.inl _) = _
    simp

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace NNReal Topology

lemma joint_laplace_as_conditional {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (r ρ L : ℝ) (y : Point d) (θ : JointPoint d) :
    Appell.laplace (jointConditionalLaw F x r ρ y L) (fun _ => (1:ℝ)) θ=
      conditionalMeanScalar F x r ρ (fun z => Real.exp (inner ℝ θ
        (jointImage (primitiveField F x r) L z))) y := by
  have hs := (jointImage_contDiff (primitiveField_contDiff hF x r) L).continuous
  rw [Appell.laplace,jointConditionalLaw,integral_map hs.aemeasurable (by fun_prop)]
  simp only [smul_eq_mul,mul_one,conditionalMeanScalar]

lemma joint_laplace_shift {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (L : ℝ) (y h : Point d) (θ : JointPoint d) :
    Appell.laplace (jointConditionalLaw F x r ρ (y+h) L) (fun _ => (1:ℝ)) θ=
      Appell.laplace (jointConditionalLaw F x r ρ y L) (fun _ => (1:ℝ))
        (θ+jointPosition d ((ρ/(1-ρ^2)) • h)) /
      Appell.laplace (jointConditionalLaw F x r ρ y L) (fun _ => (1:ℝ))
        (jointPosition d ((ρ/(1-ρ^2)) • h)) := by
  rw [joint_laplace_as_conditional hF,conditionalMeanScalar_shift hF x hr hl hρ0 hρ1]
  simp only [Appell.normalizedLaplace,div_eq_mul_inv]
  rw [mul_comm]
  congr 1
  · rw [joint_laplace_as_conditional hF]
    unfold Appell.laplace conditionalMeanScalar
    congr 1
    funext z
    dsimp only
    rw [inner_add_left,Real.exp_add,jointPosition_inner]
    simp only [smul_eq_mul]
    ring
  · congr 1
    symm
    exact joint_laplace_one (primitiveField_contDiff hF x r).continuous L _

lemma joint_log_laplace_shift {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (y h : Point d) (θ : JointPoint d) :
    Real.log (Appell.laplace (jointConditionalLaw F x r ρ (y+h) ((lam:ℝ)*r))
      (fun _ => (1:ℝ)) θ)=
      Real.log (Appell.laplace (jointConditionalLaw F x r ρ y ((lam:ℝ)*r))
        (fun _ => (1:ℝ)) (θ+jointPosition d ((ρ/(1-ρ^2)) • h)))-
      Real.log (Appell.laplace (jointConditionalLaw F x r ρ y ((lam:ℝ)*r))
        (fun _ => (1:ℝ)) (jointPosition d ((ρ/(1-ρ^2)) • h))) := by
  obtain ⟨hp,hm,_⟩ := jointConditionalLaw_properties hF x hr hlam hl hρ0 hρ1 y
  let := hp
  rw [joint_laplace_shift hF x hr.le hl hρ0 hρ1]
  exact Real.log_div (Appell.laplace_one_pos hm _).ne' (Appell.laplace_one_pos hm _).ne'

lemma joint_log_laplace_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (y : Point d) : ContDiff ℝ (⊤ : ℕ∞) (fun θ => Real.log
      (Appell.laplace (jointConditionalLaw F x r ρ y ((lam:ℝ)*r))
        (fun _ => (1:ℝ)) θ)) := by
  obtain ⟨hp,hm,_⟩ := jointConditionalLaw_properties hF x hr hlam hl hρ0 hρ1 y
  let := hp
  exact (Appell.contDiff_laplace hm continuous_const (Appell.HasGrowth.const _)).log
    (fun θ => (Appell.laplace_one_pos hm θ).ne')

lemma jointCumulant_shift {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (y h : Point d) {ι : Type*} (v : ι → JointPoint d) (l : List ι) (hlne : l≠[]) :
    jointCumulant F x r ρ ((lam:ℝ)*r) v l (y+h)=
      JetCalculus.jet v l (fun θ => Real.log
        (Appell.laplace (jointConditionalLaw F x r ρ y ((lam:ℝ)*r))
          (fun _ => (1:ℝ)) θ)) (jointPosition d ((ρ/(1-ρ^2)) • h)) := by
  let g := fun θ => Real.log (Appell.laplace
    (jointConditionalLaw F x r ρ y ((lam:ℝ)*r)) (fun _ => (1:ℝ)) θ)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := joint_log_laplace_smooth hF x hr hlam hl hρ0 hρ1 y
  have he : (fun θ => Real.log (Appell.laplace
      (jointConditionalLaw F x r ρ (y+h) ((lam:ℝ)*r)) (fun _ => (1:ℝ)) θ))=
      fun θ => g (θ+jointPosition d ((ρ/(1-ρ^2)) • h))-
        g (jointPosition d ((ρ/(1-ρ^2)) • h)) := by
    funext θ
    exact joint_log_laplace_shift hF x hr hlam hl hρ0 hρ1 y h θ
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun θ => g (θ+jointPosition d ((ρ/(1-ρ^2)) • h))) :=
    hg.comp (contDiff_id.add contDiff_const)
  unfold jointCumulant
  rw [he,JetCalculus.jet_sub hcomp (contDiff_const (c:=g (jointPosition d ((ρ/(1-ρ^2)) • h)))),
    JetCalculus.jet_const]
  simp only [hlne,↓reduceIte,sub_zero]
  have hh := congrFun (JetCalculus.jet_comp_affine hg
    (ContinuousLinearMap.id ℝ (JointPoint d)) (jointPosition d ((ρ/(1-ρ^2)) • h)) v l) 0
  simpa only [ContinuousLinearMap.id_apply,zero_add] using hh

lemma jointCumulant_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {ι : Type*} (v : ι → JointPoint d) (l : List ι) (hlne : l≠[]) :
    ContDiff ℝ (⊤ : ℕ∞) (jointCumulant F x r ρ ((lam:ℝ)*r) v l) := by
  have hg := JetCalculus.smooth_jet (joint_log_laplace_smooth hF x hr hlam hl hρ0 hρ1 0) v l
  have he : jointCumulant F x r ρ ((lam:ℝ)*r) v l =
      fun y => JetCalculus.jet v l (fun θ => Real.log (Appell.laplace
        (jointConditionalLaw F x r ρ 0 ((lam:ℝ)*r)) (fun _ => (1:ℝ)) θ))
        (jointPosition d ((ρ/(1-ρ^2)) • y)) := by
    funext y
    simpa only [zero_add] using jointCumulant_shift hF x hr hlam hl hρ0 hρ1 0 y v l hlne
  rw [he]
  exact hg.comp (by fun_prop)

lemma jointCumulant_spatial_jet {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (y : Point d) {ι κ : Type*} (v : ι → JointPoint d) (l : List ι) (hlne : l≠[])
    (w : κ → Point d) (k : List κ) :
    JetCalculus.jet w k (jointCumulant F x r ρ ((lam:ℝ)*r) v l) y=
      (ρ/(1-ρ^2))^k.length * JetCalculus.jet (fun i => jointPosition d (w i)) k
        (JetCalculus.jet v l (fun θ => Real.log (Appell.laplace
          (jointConditionalLaw F x r ρ y ((lam:ℝ)*r)) (fun _ => (1:ℝ)) θ))) 0 := by
  let g := fun θ => Real.log (Appell.laplace
    (jointConditionalLaw F x r ρ y ((lam:ℝ)*r)) (fun _ => (1:ℝ)) θ)
  have hg := JetCalculus.smooth_jet (joint_log_laplace_smooth hF x hr hlam hl hρ0 hρ1 y) v l
  let B : Point d →L[ℝ] JointPoint d := (ρ/(1-ρ^2)) • jointPosition d
  have hs := jointCumulant_smooth hF x hr hlam hl hρ0 hρ1 v l hlne
  have htrans := congrFun (JetCalculus.jet_comp_affine hs
    (ContinuousLinearMap.id ℝ (Point d)) y w k) 0
  have he : (fun h => jointCumulant F x r ρ ((lam:ℝ)*r) v l (h+y))=
      fun h => JetCalculus.jet v l g (B h+0) := by
    funext h
    simpa only [add_comm h y,B,smul_apply,map_smul,add_zero]
      using jointCumulant_shift hF x hr hlam hl hρ0 hρ1 y h v l hlne
  simp only [ContinuousLinearMap.id_apply,zero_add] at htrans
  rw [←htrans,he,JetCalculus.jet_comp_affine hg B 0]
  simp only [map_zero,zero_add]
  have hB : (fun i => B (w i))=fun i => (ρ/(1-ρ^2)) • jointPosition d (w i) := rfl
  rw [hB,JetCalculus.jet_smul hg]

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

universe u

lemma normalizedTensor_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {S : Type u} [Fintype S] (mask : S → Bool) (l : List S) (hlne : l≠[])
    (c : S → Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => normalizedTensor F x r ρ ((lam:ℝ)*r) y mask l c) :=
  contDiff_const.mul (jointCumulant_smooth hF x hr hlam hl hρ0 hρ1 _ l hlne)

lemma normalizedTensor_spatial_jet {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (y : Point d) {S K : Type u} [Fintype S] [Fintype K]
    (mask : S → Bool) (l : List S) (hlne : l≠[]) (hS : 0<Fintype.card S)
    (k : List K) (hklen : k.length=Fintype.card K) (c : K ⊕ S → Fin d) :
    JetCalculus.jet (fun i => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl i))) k
      (fun y => normalizedTensor F x r ρ ((lam:ℝ)*r) y mask l (fun s => c (Sum.inr s))) y=
      ρ^(Fintype.card K)*normalizedTensor F x r ρ ((lam:ℝ)*r) y
        (Sum.elim (fun _ => false) mask) (k.map Sum.inl++l.map Sum.inr) c := by
  let g := fun θ => Real.log (Appell.laplace
    (jointConditionalLaw F x r ρ y ((lam:ℝ)*r)) (fun _ => (1:ℝ)) θ)
  let v := fun s => EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ
    (conditionalSlotEmbedding d mask (fun s => c (Sum.inr s)) s)
  let w := fun i => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl i))
  have hs := jointCumulant_smooth hF x hr hlam hl hρ0 hρ1 v l hlne
  change JetCalculus.jet w k (fun y => ((1-ρ^2)^(Fintype.card S-1))⁻¹*
    jointCumulant F x r ρ ((lam:ℝ)*r) v l y) y=_
  rw [JetCalculus.jet_const_mul hs]
  dsimp only
  rw [jointCumulant_spatial_jet hF x hr hlam hl hρ0 hρ1 y v l hlne w k]
  have he : (fun t : K ⊕ S => EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ
      (conditionalSlotEmbedding d (Sum.elim (fun _ => false) mask) c t))=
      Sum.elim (fun i => jointPosition d (w i)) v := by
    funext t
    cases t with
    | inl i =>
      change EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ (Sum.inl (c (Sum.inl i)))=_
      exact (jointPosition_basis _).symm
    | inr s => rfl
  unfold normalizedTensor
  rw [he,JetCalculus.jet_append,JetCalculus.jet_map,JetCalculus.jet_map]
  simp only [Function.comp_def,Sum.elim_inl,Sum.elim_inr,Fintype.card_sum,hklen]
  have ha : 1-ρ^2≠0 := (probability_time hρ0 hρ1).1.ne'
  have hn : Fintype.card K+Fintype.card S-1=(Fintype.card S-1)+Fintype.card K := by omega
  rw [hn,pow_add,div_pow]
  field_simp

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_DirectionalBasisSum
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

universe u

lemma normalizedTensor_spatial_allSplit {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (y : Point d) {S K : Type u} [Fintype S] [Fintype K]
    (mask : S → Bool) (l : List S) (hlne : l≠[])
    (hlN : l.Nodup) (hlall : ∀s,s∈l) (k : List K) (hkN : k.Nodup) (hkall : ∀i,i∈k) :
    TensorEnergy.AllSplitBound (fun c : K ⊕ S → Fin d =>
      JetCalculus.jet (fun i => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl i))) k
        (fun y => normalizedTensor F x r ρ ((lam:ℝ)*r) y mask l (fun s => c (Sum.inr s))) y)
      (normalizedTensorMajorant (Fintype.card K+Fintype.card S) (1-ρ^2)) := by
  have hS : 0<Fintype.card S := by
    rw [←list_length_full l hlN hlall]
    exact List.length_pos_iff.mpr hlne
  have he := normalizedTensor_spatial_jet hF x hr hlam hl hρ0 hρ1 y mask l hlne hS
    k (list_length_full k hkN hkall)
  simp_rw [he]
  have hN : (k.map Sum.inl++l.map Sum.inr).Nodup := JetCalculus.nodup_sum_append hkN hlN
  have hall : ∀t : K ⊕ S,t∈k.map Sum.inl++l.map Sum.inr := by
    intro t
    cases t <;> simp [hkall,hlall]
  have hh := (normalizedTensor_allSplit hF x hr hlam hl hρ0 hρ1 y
    (Sum.elim (fun _ => false) mask) (k.map Sum.inl++l.map Sum.inr) hN hall).const_mul
    (ρ^(Fintype.card K))
  simp only [Fintype.card_sum] at hh
  apply hh.mono (mul_nonneg (pow_nonneg hρ0 _) (normalizedTensorMajorant_nonneg _ _))
  exact mul_le_of_le_one_left (normalizedTensorMajorant_nonneg _ _)
    (pow_le_one₀ hρ0 hρ1.le)

lemma normalizedTensor_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {S : Type} [Fintype S] (mask : S → Bool) (l : List S)
    (hlN : l.Nodup) (hlall : ∀s,s∈l) (hS : 2≤Fintype.card S) (c : S → Fin d) :
    PolySmooth (fun y => normalizedTensor F x r ρ ((lam:ℝ)*r) y mask l c) := by
  have hlne : l≠[] := by
    intro he
    have hh := list_length_full l hlN hlall
    simp [he] at hh
    omega
  apply PolySmooth.of_basis_growth (normalizedTensor_smooth hF x hr hlam hl hρ0 hρ1 mask l hlne c)
  intro k
  apply growth_of_bounded (normalizedTensorMajorant_nonneg (k.length+Fintype.card S) (1-ρ^2))
  intro y
  have hh := (normalizedTensor_spatial_allSplit hF x hr hlam hl hρ0 hρ1 y mask l hlne hlN hlall
    (List.finRange k.length) (List.nodup_finRange _) (by simp)).entry_le
      (normalizedTensorMajorant_nonneg _ _) (by simp only [Fintype.card_sum,Fintype.card_fin]; omega)
      (Sum.elim k.get c)
  simp only [Sum.elim_inl,Sum.elim_inr,Fintype.card_fin] at hh
  change |JetCalculus.jet ((EuclideanSpace.basisFun (Fin d) ℝ) ∘ k.get)
    (List.finRange k.length) (fun y => normalizedTensor F x r ρ ((lam:ℝ)*r) y mask l c) y|≤_ at hh
  rw [←JetCalculus.jet_map, List.map_get_finRange] at hh
  exact hh

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma conditionalFieldMean_jet_normalized {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (y : Point d) {S : Type} [Fintype S] (l : List S) (hlen : l.length=Fintype.card S)
    (c : S ⊕ Unit → Fin d) :
    JetCalculus.jet (fun s => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl s))) l
      (fun y => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ())))
        (conditionalFieldMean F x r ρ y)) y=
      ρ^(Fintype.card S)*((lam:ℝ)*r)*normalizedTensor F x r ρ ((lam:ℝ)*r) y
        (Sum.elim (fun _ => false) (fun _ => true)) (l.map Sum.inl++[Sum.inr ()]) c := by
  have hi : (fun y => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ())))
      (conditionalFieldMean F x r ρ y))=
      conditionalMeanScalar F x r ρ (fun z => inner ℝ
        (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ()))) (primitiveField F x r z)) :=
    funext (conditionalFieldMean_inner hF x hr.le hl hρ0 hρ1 _)
  rw [hi,conditionalFieldMean_jet_U hF x hr hlam hl hρ0 hρ1]
  unfold conditionalU normalizedTensor
  rw [JetCalculus.jet_append,JetCalculus.jet_map]
  simp only [Fintype.card_sum,Fintype.card_unique,add_tsub_cancel_right,hlen,
    Function.comp_def]
  have hv : (fun s => jointPosition d (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl s))))=
      (fun s => EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ
        (conditionalSlotEmbedding d (Sum.elim (fun _ => false) (fun _ => true)) c (Sum.inl s))) := by
    funext s
    exact jointPosition_basis _
  rw [hv,jointField_basis]
  have he : conditionalSlotEmbedding d (Sum.elim (fun _ : S => false) (fun _ : Unit => true)) c
      (Sum.inr ())=Sum.inr (c (Sum.inr ())) := rfl
  simp only [JetCalculus.jet,he]
  ring

lemma conditionalFieldMean_component_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (i : Fin d) : PolySmooth (fun y => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
      (conditionalFieldMean F x r ρ y)) := by
  let v := EuclideanSpace.basisFun (Fin d) ℝ i
  have hs := (innerSL ℝ v).contDiff.comp (conditionalFieldMean_smooth hF x hr.le hl hρ0 hρ1)
  apply PolySmooth.of_basis_growth hs
  intro k
  by_cases hk : k=[]
  · subst k
    exact growth_of_lipschitz ((innerSL ℝ v).lipschitz.comp
      (conditionalFieldMean_lipschitz hF x hr.le hl hρ0 hρ1))
  · let c : Fin k.length ⊕ Unit → Fin d := Sum.elim k.get (fun _ => i)
    have he : JetCalculus.jet (EuclideanSpace.basisFun (Fin d) ℝ) k
        (fun y => inner ℝ v (conditionalFieldMean F x r ρ y))=
        fun y => ρ^k.length*((lam:ℝ)*r)*normalizedTensor F x r ρ ((lam:ℝ)*r) y
          (Sum.elim (fun _ => false) (fun _ => true))
          ((List.finRange k.length).map Sum.inl++[Sum.inr ()]) c := by
      funext y
      have hh := conditionalFieldMean_jet_normalized hF x hr hlam hl hρ0 hρ1 y
        (List.finRange k.length) (by simp) c
      simp only [c,Sum.elim_inl,Sum.elim_inr,Fintype.card_fin] at hh
      change JetCalculus.jet ((EuclideanSpace.basisFun (Fin d) ℝ) ∘ k.get)
        (List.finRange k.length) _ y=_ at hh
      rw [←JetCalculus.jet_map,List.map_get_finRange] at hh
      exact hh
    change HasPolynomialGrowth (JetCalculus.jet (EuclideanSpace.basisFun (Fin d) ℝ) k
      (fun y => inner ℝ v (conditionalFieldMean F x r ρ y)))
    rw [he]
    apply Appell.HasGrowth.mul (growth_const _)
    have hN : ((List.finRange k.length).map (Sum.inl : Fin k.length → Fin k.length ⊕ Unit)++
        [Sum.inr ()]).Nodup := by
      simpa using JetCalculus.nodup_sum_append (List.nodup_finRange k.length)
        (by simp : ([()] : List Unit).Nodup)
    have hall : ∀t : Fin k.length ⊕ Unit,t∈(List.finRange k.length).map Sum.inl++[Sum.inr ()] := by
      intro t; cases t <;> simp
    exact (normalizedTensor_polySmooth hF x hr hlam hl hρ0 hρ1 _ _ hN hall
      (by simp; exact List.length_pos_iff.mpr hk) c).growth []

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_GadjScalar
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma dir_mean_jet_eq_scaled_U {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {κ : Type*} (v : κ → Point d) (l : List κ) (i k : Fin d) :
    JetCalculus.dir (JetCalculus.spaceBasis d k)
      (JetCalculus.jet v l (fun z => jointMean F x r i (ρ,z)))=
      fun y => ρ^(l.length+1)*conditionalU F x r ρ y (EuclideanSpace.basisFun (Fin d) ℝ i)
        ((lam:ℝ)*r) (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k))
          (Sum.inr ()::l.map Sum.inl) := by
  have hh := mean_jet_eq_scaled_U hF x hr hlam hl hρ0 hρ1
    (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k)) (Sum.inr ()::l.map Sum.inl) i
  simpa only [JetCalculus.jet,JetCalculus.jet_map,Function.comp_def,Sum.elim_inl,Sum.elim_inr,
    List.length_cons,List.length_map] using hh

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_JetRightSlice
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma joint_mean_transport {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    (y : Point d) (i : Fin d) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (jointMean F x r i) (ρ,y)=
      ρ⁻¹*JetCalculus.gadj jointSpace (jointScore F x r)
        (fun k => JetCalculus.dir (jointSpace k) (jointMean F x r i)) (ρ,y) := by
  have hp : ρ^2<1 := by nlinarith
  have hMi := jointMean_smooth_at hF x hr.le hl (p:=(ρ,y)) hp i
  have hm := joint_mdir_eq_material F x r (hMi.differentiableAt (by simp))
  change JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (jointMean F x r i) (ρ,y)=_ at hm
  rw [hm]
  change materialScalar F x r (fun t y => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
    (conditionalFieldMean F x r t y)) ρ y=_
  rw [material_conditionalFieldMean hF x hr hlam hl hρ0.le hρ1]
  have he : (fun k y => conditionalU F x r ρ y (EuclideanSpace.basisFun (Fin d) ℝ i)
      ((lam:ℝ)*r) (fun _ : Unit => EuclideanSpace.basisFun (Fin d) ℝ k) [()])=
      fun k y => ρ⁻¹*JetCalculus.dir (EuclideanSpace.basisFun (Fin d) ℝ k)
        (fun z => jointMean F x r i (ρ,z)) y := by
    funext k
    exact conditionalU_one_eq_dir hF x hr hlam hl hρ0 hρ1 _ _
  have hD (k : Fin d) : Differentiable ℝ (JetCalculus.dir (EuclideanSpace.basisFun (Fin d) ℝ k)
      (fun z => jointMean F x r i (ρ,z))) :=
    (JetCalculus.smooth_dir ((innerSL ℝ _).contDiff.comp
      (conditionalFieldMean_smooth hF x hr.le hl hρ0.le hρ1)) _).differentiable (by simp)
  rw [he,tensorAdjoint_scalar _ _ hD]
  rw [joint_gadj_slice hF x hr.le hl hρ0.le hρ1 (fun k =>
    (JetCalculus.smooth_dir_at hMi _).differentiableAt (by simp))]
  have he' : (fun k => JetCalculus.dir (EuclideanSpace.basisFun (Fin d) ℝ k)
      (fun z => jointMean F x r i (ρ,z)))=
      fun k z => JetCalculus.dir (jointSpace k) (jointMean F x r i) (ρ,z) := by
    funext k z
    exact JetCalculus.dir_right_slice_at
      ((jointMean_smooth_at hF x hr.le hl (p:=(ρ,z)) hp i).differentiableAt (by simp)) _
  rw [he']

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

open JetCalculus in
theorem material_mean_jet {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    {κ : Type*} [DecidableEq κ] (v : κ → Point d) (l : List κ) (hlN : l.Nodup)
    (i : Fin d) (y : Point d) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
      (JetCalculus.jet (fun j => (0,v j)) l (jointMean F x r i)) (ρ,y)=
      ρ⁻¹*JetCalculus.gadj (JetCalculus.spaceBasis d) (fun k z => jointScore F x r k (ρ,z))
        (fun k => JetCalculus.dir (JetCalculus.spaceBasis d k)
          (JetCalculus.jet v l (fun z => jointMean F x r i (ρ,z)))) y+
        (l.length:ℝ)*ρ⁻¹*JetCalculus.jet v l (fun z => jointMean F x r i (ρ,z)) y+
        2*r*∑s∈l.toFinset.powerset.erase ∅,∑k,
          JetCalculus.jet v (l.filter (fun j => j∈s)) (fun z => jointMean F x r k (ρ,z)) y*
            JetCalculus.dir (JetCalculus.spaceBasis d k)
              (JetCalculus.jet v (l.filter (fun j => j∉s)) (fun z => jointMean F x r i (ρ,z))) y := by
  have hp : ρ^2<1 := by nlinarith
  have hJ (k : Fin d) (z : Point d) : ContDiffAt ℝ (⊤:ℕ∞) (jointMean F x r k) (ρ,z) :=
    jointMean_smooth_at hF x hr.le hl hp k
  have hS (k : Fin d) : ContDiff ℝ (⊤:ℕ∞) (fun z => jointMean F x r k (ρ,z)) :=
    (innerSL ℝ _).contDiff.comp (conditionalFieldMean_smooth hF x hr.le hl hρ0.le hρ1)
  have hs (k : Fin d) (a : List κ) := JetCalculus.jet_right_slice_at (hJ k) v a
  have hds (k : Fin d) (a : List κ) (j : Fin d) (z : Point d) :
      JetCalculus.dir (jointSpace j) (JetCalculus.jet (fun j => (0,v j)) a (jointMean F x r k)) (ρ,z)=
      JetCalculus.dir (JetCalculus.spaceBasis d j)
        (JetCalculus.jet v a (fun z => jointMean F x r k (ρ,z))) z := by
    rw [hs]
    exact (JetCalculus.dir_right_slice_at
      ((JetCalculus.smooth_jet_at (hJ k z) _ a).differentiableAt (by simp)) _).symm
  have hbase : (fun z => JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
      (jointMean F x r i) (ρ,z))=fun z =>
      ρ⁻¹*JetCalculus.gadj (JetCalculus.spaceBasis d)
        (fun k z => jointScore F x r k (ρ,z))
        (fun k => JetCalculus.dir (JetCalculus.spaceBasis d k) (fun z => jointMean F x r i (ρ,z))) z := by
    funext z
    rw [joint_mean_transport hF x hr hlam hl hρ0 hρ1]
    have ht := JetCalculus.gadj_right_slice_at (JetCalculus.spaceBasis d) (jointScore F x r)
      (V:=fun k => JetCalculus.dir (jointSpace k) (jointMean F x r i))
      (fun k => (JetCalculus.smooth_dir_at (hJ i z) _).differentiableAt (by simp))
    change JetCalculus.gadj jointSpace (jointScore F x r)
      (fun k => JetCalculus.dir (jointSpace k) (jointMean F x r i)) (ρ,z)=_ at ht
    rw [ht]
    have hd : (fun k w => JetCalculus.dir (jointSpace k) (jointMean F x r i) (ρ,w))=
        fun k => JetCalculus.dir (JetCalculus.spaceBasis d k) (fun w => jointMean F x r i (ρ,w)) := by
      funext k w
      exact hds i [] k w
    rw [hd]
  have hDj := JetCalculus.jet_right_slice_at (fun z => JetCalculus.smooth_mdir_at (1,0)
    jointSpace r (fun k => hJ k z) (hJ i z)) v l
  have hg : ContDiff ℝ (⊤:ℕ∞) (JetCalculus.gadj (JetCalculus.spaceBasis d)
      (fun k z => jointScore F x r k (ρ,z))
      (fun k => JetCalculus.dir (JetCalculus.spaceBasis d k) (fun z => jointMean F x r i (ρ,z)))) :=
    ContDiff.sum fun k _ => JetCalculus.smooth_cadj _ (by
      change ContDiff ℝ (⊤:ℕ∞) (fun z => JetCalculus.linearScore k z+(r*ρ)*jointMean F x r k (ρ,z))
      exact (JetCalculus.linearScore_smooth k).add (contDiff_const.mul (hS k)))
      (JetCalculus.smooth_dir (hS i) _)
  have hj := congrFun (JetCalculus.jet_gadj_gradient hS (hS i) (r*ρ) v l hlN) y
  change JetCalculus.jet v l (JetCalculus.gadj (JetCalculus.spaceBasis d)
    (fun k z => jointScore F x r k (ρ,z))
    (fun k => JetCalculus.dir (JetCalculus.spaceBasis d k) (fun z => jointMean F x r i (ρ,z)))) y=_ at hj
  rw [JetCalculus.mdir_jet_time _ _ _ (jointMean_timeSmooth hF x hr.le hl)
    (jointMean_timeSmooth hF x hr.le hl i) (fun j => (0,v j)) l hlN (by dsimp; linarith) hρ1]
  rw [←congrFun hDj y,hbase,JetCalculus.jet_const_mul hg]
  dsimp only
  rw [hj]
  have hsub : (∑s∈l.toFinset.powerset.erase ∅,∑k,
      JetCalculus.jet (fun j => (0,v j)) (l.filter (fun j => j∈s)) (jointMean F x r k) (ρ,y)*
        JetCalculus.dir (jointSpace k)
          (JetCalculus.jet (fun j => (0,v j)) (l.filter (fun j => j∉s)) (jointMean F x r i)) (ρ,y))=
      ∑s∈l.toFinset.powerset.erase ∅,∑k,
      JetCalculus.jet v (l.filter (fun j => j∈s)) (fun z => jointMean F x r k (ρ,z)) y*
        JetCalculus.dir (JetCalculus.spaceBasis d k)
          (JetCalculus.jet v (l.filter (fun j => j∉s)) (fun z => jointMean F x r i (ρ,z))) y := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro k _
    rw [←congrFun (hs k _) y,hds]
  rw [hsub]
  simp only [jointScore,JetCalculus.linearScore,JetCalculus.spaceBasis]
  field_simp [hρ0.ne']
  ring

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ScaledMeanJet
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

def scaledMeanJet {d : ℕ} {κ : Type*} (F : Point d → ℝ) (x : Point d) (r : ℝ)
    (v : κ → Point d) (l : List κ) (i : Fin d) (p : ℝ × Point d) : ℝ :=
  (p.1^l.length)⁻¹*JetCalculus.jet (fun j => (0,v j)) l (jointMean F x r i) p

lemma scaledMeanJet_eq_U {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    {κ : Type*} (v : κ → Point d) (l : List κ) (i : Fin d) (y : Point d) :
    scaledMeanJet F x r v l i (ρ,y)=
      conditionalU F x r ρ y (EuclideanSpace.basisFun (Fin d) ℝ i) ((lam:ℝ)*r) v l := by
  have hp : ρ^2<1 := by nlinarith
  have hj := JetCalculus.jet_right_slice_at (fun z => jointMean_smooth_at hF x hr.le hl (p:=(ρ,z)) hp i) v l
  have hm : conditionalMeanScalar F x r ρ
      (fun z => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i) (primitiveField F x r z))=
      fun z => jointMean F x r i (ρ,z) :=
    (funext (conditionalFieldMean_inner hF x hr.le hl hρ0.le hρ1 _)).symm
  have hU := conditionalFieldMean_jet_U hF x hr hlam hl hρ0.le hρ1
    (EuclideanSpace.basisFun (Fin d) ℝ i) y v l
  rw [hm] at hU
  unfold scaledMeanJet
  rw [←congrFun hj y,hU]
  field_simp [hρ0.ne']

theorem material_scaledMeanJet {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    {κ : Type*} [DecidableEq κ] (v : κ → Point d) (l : List κ) (hlN : l.Nodup)
    (i : Fin d) (y : Point d) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (scaledMeanJet F x r v l i) (ρ,y)=
      (ρ^(l.length+1))⁻¹*JetCalculus.gadj (JetCalculus.spaceBasis d)
        (fun k z => jointScore F x r k (ρ,z))
        (fun k => JetCalculus.dir (JetCalculus.spaceBasis d k)
          (JetCalculus.jet v l (fun z => jointMean F x r i (ρ,z)))) y+
        2*r*(ρ^l.length)⁻¹*∑s∈l.toFinset.powerset.erase ∅,∑k,
          JetCalculus.jet v (l.filter (fun j => j∈s)) (fun z => jointMean F x r k (ρ,z)) y*
            JetCalculus.dir (JetCalculus.spaceBasis d k)
              (JetCalculus.jet v (l.filter (fun j => j∉s)) (fun z => jointMean F x r i (ρ,z))) y := by
  have hp : ρ^2<1 := by nlinarith
  have hJ (z : Point d) := jointMean_smooth_at hF x hr.le hl (p:=(ρ,z)) hp i
  have hc := JetCalculus.hasDerivAt_inv_nat_pow hρ0.ne' l.length
  have he := JetCalculus.mdir_time_mul_at (JetCalculus.spaceBasis d) r (jointMean F x r)
    hc.differentiableAt ((JetCalculus.smooth_jet_at (hJ y) (fun j => (0,v j)) l).differentiableAt (by simp))
  change JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (scaledMeanJet F x r v l i) (ρ,y)=_ at he
  rw [he,hc.deriv]
  change -↑l.length*ρ⁻¹*(ρ^l.length)⁻¹*JetCalculus.jet (fun j => (0,v j)) l (jointMean F x r i) (ρ,y)+
    (ρ^l.length)⁻¹*JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
      (JetCalculus.jet (fun j => (0,v j)) l (jointMean F x r i)) (ρ,y)=_
  rw [material_mean_jet hF x hr hlam hl hρ0 hρ1 v l hlN i y]
  rw [←congrFun (JetCalculus.jet_right_slice_at hJ v l) y]
  simp only [pow_succ,mul_inv_rev]
  ring

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_JointU
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Filter
open scoped Topology Classical BigOperators NNReal RealInnerProductSpace

lemma jointU_eventually_scaled {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    {κ : Type*} (v : κ → Point d) (l : List κ) (i : Fin d) (y : Point d) :
    jointU F x r ((lam:ℝ)*r) v l i=ᶠ[nhds (ρ,y)]scaledMeanJet F x r v l i := by
  have hn : ∀ᶠp : ℝ × Point d in nhds (ρ,y),p.1∈Set.Ioo (0:ℝ) 1 :=
    continuousAt_fst.eventually (Ioo_mem_nhds hρ0 hρ1)
  filter_upwards [hn] with p hp
  exact (scaledMeanJet_eq_U hF x hr hlam hl hp.1 hp.2 v l i p.2).symm

theorem material_conditionalU_pos {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    {κ : Type*} [DecidableEq κ] (v : κ → Point d) (l : List κ) (hlN : l.Nodup)
    (i : Fin d) (y : Point d) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
      (jointU F x r ((lam:ℝ)*r) v l i) (ρ,y)=
      JetCalculus.gadj (JetCalculus.spaceBasis d) (fun k z => jointScore F x r k (ρ,z))
        (fun k z => jointU F x r ((lam:ℝ)*r)
          (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k)) (Sum.inr ()::l.map Sum.inl) i (ρ,z)) y+
      2*r*ρ*∑s∈l.toFinset.powerset.erase ∅,∑k,
        jointU F x r ((lam:ℝ)*r) v (l.filter (fun j => j∈s)) k (ρ,y)*
          jointU F x r ((lam:ℝ)*r) (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k))
            (Sum.inr ()::(l.filter (fun j => j∉s)).map Sum.inl) i (ρ,y) := by
  have he := (JetCalculus.mdir_eventuallyEq (1,0) jointSpace r (M:=jointMean F x r) (fun _ => EventuallyEq.rfl)
    (jointU_eventually_scaled hF x hr hlam hl hρ0 hρ1 v l i y)).eq_of_nhds
  rw [he,material_scaledMeanJet hF x hr hlam hl hρ0 hρ1 v l hlN]
  have hU (k : Fin d) := conditionalU_smooth_pos hF x hr hlam hl hρ0 hρ1
    (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k)) (Sum.inr ()::l.map Sum.inl)
      (EuclideanSpace.basisFun (Fin d) ℝ i)
  have hdir := dir_mean_jet_eq_scaled_U hF x hr hlam hl hρ0.le hρ1 v l i
  simp_rw [hdir]
  rw [JetCalculus.gadj_scalar _ _ (fun k => (hU k).differentiable (by simp))]
  dsimp only
  have hscale : (ρ^(l.length+1))⁻¹*ρ^(l.length+1)=1 := inv_mul_cancel₀ (pow_ne_zero _ hρ0.ne')
  rw [←mul_assoc,hscale,one_mul]
  congr 1
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [mean_jet_eq_scaled_U hF x hr hlam hl hρ0.le hρ1,
    dir_mean_jet_eq_scaled_U hF x hr hlam hl hρ0.le hρ1]
  dsimp only
  have hs := split_power_cancel l s hρ0.ne'
  unfold jointU
  calc
    _ = 2*r*((ρ^l.length)⁻¹*ρ^(l.filter (fun j => j∈s)).length*
        ρ^((l.filter (fun j => j∉s)).length+1))*
        (conditionalU F x r ρ y (EuclideanSpace.basisFun (Fin d) ℝ k) ((lam:ℝ)*r) v
          (l.filter (fun j => j∈s))*conditionalU F x r ρ y (EuclideanSpace.basisFun (Fin d) ℝ i)
            ((lam:ℝ)*r) (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k))
              (Sum.inr ()::(l.filter (fun j => j∉s)).map Sum.inl)) := by ring
    _ = _ := by rw [hs]

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TerminalBackward
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory ProbabilityTheory
open scoped Topology NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

lemma probabilityTransport_cocycle (s t u : Icc (0:ℝ) T) (z : Point d) :
    probabilityTransport hF x hr hl hT0 hT1 t u
      (probabilityTransport hF x hr hl hT0 hT1 s t z)=
      probabilityTransport hF x hr hl hT0 hT1 s u z :=
  GlobalODE.flow_cocycle _ _ s t u z
lemma probabilityTransport_initial (s : Icc (0:ℝ) T) (z : Point d) :
    probabilityTransport hF x hr hl hT0 hT1 s s z=z := GlobalODE.flow_initial _ _ s z
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function Filter
open scoped Topology NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

lemma terminalBackward_smooth : ContDiff ℝ (⊤:ℕ∞) (terminalBackward hF x hr hl hT0 hT1) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hclip : ContDiff ℝ (⊤:ℕ∞) (smoothTimeClip hT0 hT1) :=
    contDiff_infty.mpr (smoothTimeClip_contDiff hT0 hT1)
  exact (GlobalODE.smooth_flow_joint (smoothProbabilityVelocity_smooth hF x hr hl hT0 hT1)
    (fun u (_ : u∈Icc (-1) (T+1)) => smoothProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
    ⟨T,by constructor <;> linarith⟩ (smoothTimeClip hT0 hT1 p.1,p.2)
    (smoothTimeClip_mem_extended hT0 hT1 p.1)).comp p
      ((hclip.comp contDiff_fst).prodMk contDiff_snd).contDiffAt

lemma terminalForward_smooth : ContDiff ℝ (⊤:ℕ∞) (terminalForward hF x hr hl hT0 hT1) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hclip : ContDiff ℝ (⊤:ℕ∞) (smoothTimeClip hT0 hT1) :=
    contDiff_infty.mpr (smoothTimeClip_contDiff hT0 hT1)
  exact (GlobalODE.backward_flow_smooth (smoothProbabilityVelocity_smooth hF x hr hl hT0 hT1)
    (by linarith : (-1:ℝ)≤T+1)
    (fun u (_ : u∈Icc (-1) (T+1)) => smoothProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
    ⟨T,by constructor <;> linarith⟩ (smoothTimeClip hT0 hT1 p.1,p.2)
    (smoothTimeClip_mem_extended hT0 hT1 p.1)).comp p
      ((hclip.comp contDiff_fst).prodMk contDiff_snd).contDiffAt

lemma probabilityTransport_eq_extended (s t : Icc (0:ℝ) T) (z : Point d) :
    probabilityTransport hF x hr hl hT0 hT1 s t z=
      GlobalODE.flow (a:= -1) (b:=T+1)
      (fun u _ => smoothProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
      (smoothProbabilityVelocity_smooth hF x hr hl hT0 hT1).continuous
      ⟨s,by constructor <;> linarith [s.2.1,s.2.2]⟩ z t := by
  apply GlobalODE.flow_restrict
    (clampedProbabilityVelocity_continuous hF x hr hl hT0 hT1)
    (smoothProbabilityVelocity_smooth hF x hr hl hT0 hT1).continuous
    (fun u _ => clampedProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
    (fun u _ => smoothProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
  · intro u hu
    constructor <;> linarith [hu.1,hu.2]
  · intro u hu y
    rw [clampedProbabilityVelocity_eq F x r T hT0 hu]
    dsimp [smoothProbabilityVelocity]
    rw [smoothTimeClip_eq hT0 hT1 hu]

lemma terminalBackward_eq (t : Icc (0:ℝ) T) (y : Point d) :
    terminalBackward hF x hr hl hT0 hT1 (t,y)=
      probabilityTransport hF x hr hl hT0 hT1 ⟨T,hT0,le_rfl⟩ t y := by
  rw [probabilityTransport_eq_extended]
  simp only [terminalBackward,smoothTimeClip_eq hT0 hT1 t.2]
lemma terminalForward_eq (t : Icc (0:ℝ) T) (y : Point d) :
    terminalForward hF x hr hl hT0 hT1 (t,y)=
      probabilityTransport hF x hr hl hT0 hT1 t ⟨T,hT0,le_rfl⟩ y := by
  rw [probabilityTransport_eq_extended]
  simp only [terminalForward,smoothTimeClip_eq hT0 hT1 t.2,
    projIcc_of_mem _ (show (t:ℝ)∈Icc (-1) (T+1) by constructor <;> linarith [t.2.1,t.2.2])]

lemma terminalForward_backward (t : Icc (0:ℝ) T) (y : Point d) :
    terminalForward hF x hr hl hT0 hT1 (t,terminalBackward hF x hr hl hT0 hT1 (t,y))=y := by
  rw [terminalForward_eq,terminalBackward_eq,probabilityTransport_cocycle,probabilityTransport_initial]
lemma terminalBackward_forward (t : Icc (0:ℝ) T) (y : Point d) :
    terminalBackward hF x hr hl hT0 hT1 (t,terminalForward hF x hr hl hT0 hT1 (t,y))=y := by
  rw [terminalBackward_eq,terminalForward_eq,probabilityTransport_cocycle,probabilityTransport_initial]
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_CoordinateRank
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Filter
open scoped Topology Classical BigOperators NNReal RealInnerProductSpace

theorem material_jointU {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {κ : Type*} [DecidableEq κ] (v : κ → Point d) (l : List κ) (hlN : l.Nodup)
    (i : Fin d) (y : Point d) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
      (jointU F x r ((lam:ℝ)*r) v l i) (ρ,y)=
      JetCalculus.gadj jointSpace (jointScore F x r)
        (fun k => jointU F x r ((lam:ℝ)*r)
          (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k))
            (Sum.inr ()::l.map Sum.inl) i) (ρ,y)+
      2*r*ρ*∑s∈l.toFinset.powerset.erase ∅,∑k,
        jointU F x r ((lam:ℝ)*r) v (l.filter (fun j => j∈s)) k (ρ,y)*
          jointU F x r ((lam:ℝ)*r) (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k))
            (Sum.inr ()::(l.filter (fun j => j∉s)).map Sum.inl) i (ρ,y) := by
  let U := jointU F x r ((lam:ℝ)*r) v l i
  let V := fun k => jointU F x r ((lam:ℝ)*r)
    (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k)) (Sum.inr ()::l.map Sum.inl) i
  let A := JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) U
  let B := fun p : ℝ × Point d => JetCalculus.gadj jointSpace (jointScore F x r) V p+
    2*r*p.1*∑s∈l.toFinset.powerset.erase ∅,∑k,
      jointU F x r ((lam:ℝ)*r) v (l.filter (fun j => j∈s)) k p*
        jointU F x r ((lam:ℝ)*r) (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k))
          (Sum.inr ()::(l.filter (fun j => j∉s)).map Sum.inl) i p
  change A (ρ,y)=B (ρ,y)
  have hU := jointU_timeSmooth hF x hr hlam hl v l hlN i
  have hV (k : Fin d) := jointU_timeSmooth hF x hr hlam hl
    (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k)) (Sum.inr ()::l.map Sum.inl)
      (extra_list_nodup hlN) i
  have hpos (t : ℝ) (h0 : 0<t) (h1 : t<1) : A (t,y)=B (t,y) := by
    have he := material_conditionalU_pos hF x hr hlam hl h0 h1 v l hlN i y
    have hs := JetCalculus.gadj_right_slice_at (JetCalculus.spaceBasis d) (jointScore F x r)
      (V:=V) (fun k => (hV k (t,y) (by dsimp; linarith) h1).differentiableAt (by simp))
    change JetCalculus.gadj jointSpace (jointScore F x r) V (t,y)=_ at hs
    change JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
      (jointU F x r ((lam:ℝ)*r) v l i) (t,y)=_
    rw [he]
    exact congrArg (fun a => a+2*r*t*∑s∈l.toFinset.powerset.erase ∅,∑k,
      jointU F x r ((lam:ℝ)*r) v (l.filter (fun j => j∈s)) k (t,y)*
        jointU F x r ((lam:ℝ)*r) (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k))
          (Sum.inr ()::(l.filter (fun j => j∉s)).map Sum.inl) i (t,y)) hs.symm
  rcases hρ0.eq_or_lt with hzero|hposρ
  · subst ρ
    have hz : (0:ℝ)^2<1 := by norm_num
    have hA : ContDiffAt ℝ (⊤:ℕ∞) A (0,y) :=
      JetCalculus.smooth_mdir_at (1,0) jointSpace r (jointMean_smooth_at hF x hr.le hl hz)
        (hU (0,y) (by norm_num) (by norm_num))
    have hB : ContDiffAt ℝ (⊤:ℕ∞) B (0,y) := by
      apply ContDiffAt.add
      · exact JetCalculus.smooth_gadj_at jointSpace (jointScore_smooth_at hF x hr.le hl hz)
          (fun k => hV k (0,y) (by norm_num) (by norm_num))
      · apply ContDiffAt.mul (contDiffAt_const.mul contDiffAt_fst)
        apply ContDiffAt.sum
        intro s _
        apply ContDiffAt.sum
        intro k _
        exact (jointU_timeSmooth hF x hr hlam hl v _ (hlN.filter _) k (0,y)
          (by norm_num) (by norm_num)).mul
          (jointU_timeSmooth hF x hr hlam hl _ _ (extra_list_nodup (hlN.filter _)) i (0,y)
            (by norm_num) (by norm_num))
    have hc : ContinuousAt (fun t : ℝ => (t,y)) 0 :=
      continuousAt_id.prodMk continuousAt_const
    exact eq_zero_of_continuous_pos (hA.continuousAt.comp (f:=fun t : ℝ => (t,y)) hc)
      (hB.continuousAt.comp (f:=fun t : ℝ => (t,y)) hc) hpos
  · exact hpos ρ hposρ hρ1

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_SplitIndex
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal

namespace TensorAtom
variable {S : Type} [Fintype S]

lemma material_jetList {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) (hne : l≠[])
    (c : S ⊕ Unit → Fin d) (y : Point d) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
      ((jetList l hN hall hne).eval F x r ((lam:ℝ)*r) c) (ρ,y)=
      ((extendedU l hN hall).adjoint (jetCard l hN hall hne)).eval F x r ((lam:ℝ)*r) c (ρ,y)+
      2*(r*((lam:ℝ)*r))*ρ*∑a : SplitIndex l,(splitAtom l hN hall a).eval F x r ((lam:ℝ)*r) c (ρ,y) := by
  let L : ℝ := (lam:ℝ)*r
  have hL : L≠0 := ne_of_gt (mul_pos (by exact_mod_cast hlam) hr)
  let v : S → Point d := fun s => JetCalculus.spaceBasis d (c (Sum.inl s))
  let U := jointU F x r L v l (c (Sum.inr ()))
  let V := fun k => jointU F x r L (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k))
    (Sum.inr ()::l.map Sum.inl) (c (Sum.inr ()))
  have hU := jointU_timeSmooth hF x hr hlam hl v l hN (c (Sum.inr ()))
  have hV (k : Fin d) := jointU_timeSmooth hF x hr hlam hl
    (Sum.elim v (fun _ : Unit => JetCalculus.spaceBasis d k)) _ (extra_list_nodup hN) (c (Sum.inr ()))
  have hA : ((extendedU l hN hall).adjoint (jetCard l hN hall hne)).eval F x r L c (ρ,y)=
      L⁻¹*JetCalculus.gadj jointSpace (jointScore F x r) V (ρ,y) := by
    rw [adjoint_eval]
    have he : (fun k => (extendedU l hN hall).eval F x r L (Sum.elim c (fun _ => k)))=
        fun k p => L⁻¹*V k p := by
      funext k
      rw [extendedU_eval]
      rfl
    rw [he]
    exact JetCalculus.gadj_scalar_at _ _ (fun k =>
      (hV k (ρ,y) (by dsimp; linarith) hρ1).differentiableAt (by simp)) _
  change JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
      ((jetList l hN hall hne).eval F x r L c) (ρ,y)=_
  rw [jetList_eval,JetCalculus.mdir_const_mul_at _ _ _ _
    ((hU (ρ,y) (by dsimp; linarith) hρ1).differentiableAt (by simp)),
    material_jointU hF x hr hlam hl hρ0 hρ1 v l hN,hA]
  rw [mul_add]
  congr 1
  simp only [splitAtom,splitProduct_eval]
  rw [←Finset.sum_coe_sort]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [L,v]
  field_simp [hL]

end TensorAtom
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_JetMaterial
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal

namespace TensorAtom
variable {S T : Type}

variable [Fintype S]

lemma hasMaterial_jetList (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) (hne : l≠[]) :
    (jetList l hN hall hne).HasMaterial (jetMaterial l hN hall hne) := by
  intro d F lam hF x r ρ hr hlam hl h0 h1 c y
  rw [material_jetList hF x hr hlam hl h0 h1]
  unfold jetMaterial
  rw [TensorSum.add_eval,TensorSum.pure_eval]
  congr 1
  change 2*(r*((lam:ℝ)*r))*ρ*(∑a : SplitIndex l,(splitAtom l hN hall a).eval F x r ((lam:ℝ)*r) c (ρ,y))=
    ∑a : SplitIndex l,(r*((lam:ℝ)*r))^1*(Polynomial.C (2:ℝ)*Polynomial.X).eval ρ*
      (splitAtom l hN hall a).eval F x r ((lam:ℝ)*r) c (ρ,y)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,pow_one]
  ring
end TensorAtom

namespace TensorExpression

lemma jet_atom_eval {d : ℕ} (q : ℕ) (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (c : Fin (q+2) → Fin d) :
    (jet q).atom.eval F x r L c=
      ((TensorAtom.jetList (List.finRange (q+1)) (List.nodup_finRange _) (by simp) (by simp)).relabel (TensorAtom.lastEquiv (Equiv.refl (Fin (q+1)))).symm).eval F x r L c := by
  rw [TensorAtom.relabel_eval,TensorAtom.jetList_eval]
  change (fun p => L⁻¹*jointU F x r L _ _ _ p)=_
  simp only [Function.comp_apply,TensorAtom.lastEquiv_symm_inl,TensorAtom.lastEquiv_symm_inr,Equiv.refl_symm,Equiv.refl_apply]
  rfl

lemma jet_hasMaterial (q : ℕ) : ∃B : TensorSum (Fin (q+2)),
    B.weightLE (q+2) ∧ (jet q).atom.HasMaterial B := by
  let l := List.finRange (q+1)
  let hN : l.Nodup := List.nodup_finRange _
  let hall : ∀s,s∈l := by simp [l]
  let hne : l≠[] := by simp [l]
  let e := (TensorAtom.lastEquiv (Equiv.refl (Fin (q+1)))).symm
  refine ⟨(TensorAtom.jetMaterial l hN hall hne).relabel e,?_,?_⟩
  · have h := TensorSum.weightLE_relabel (TensorAtom.jetMaterial_weight l hN hall hne) e
    simpa only [TensorAtom.jetList_weight,l,List.length_finRange,Nat.add_sub_cancel] using h
  · exact TensorAtom.HasMaterial.congr
      (TensorAtom.HasMaterial.relabel (TensorAtom.hasMaterial_jetList l hN hall hne) e) (jet_atom_eval q)
end TensorExpression
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal

namespace TensorExpression

theorem hasMaterial {n : ℕ} (A : TensorExpression n) :
    ∃B : TensorSum (Fin n), B.weightLE (A.weight+2) ∧ A.atom.HasMaterial B := by
  induction A with
  | jet q => exact jet_hasMaterial q
  | perm e A ih =>
    obtain ⟨B,hB,h⟩ := ih
    refine ⟨B.relabel e,TensorSum.weightLE_relabel hB e,?_⟩
    apply TensorAtom.HasMaterial.congr (TensorAtom.HasMaterial.relabel h e)
    intros
    rfl
  | @contract m n hm hn A B ihA ihB =>
    let : NeZero m := ⟨Nat.ne_of_gt hm⟩
    let : NeZero n := ⟨Nat.ne_of_gt hn⟩
    obtain ⟨DA,hDA,hA⟩ := ihA
    obtain ⟨DB,hDB,hB⟩ := ihB
    let eA := TensorAtom.lastEquiv (Equiv.refl (Fin m))
    let eB := TensorAtom.lastEquiv (Equiv.refl (Fin n))
    let AA := A.atom.relabel eA
    let BB := B.atom.relabel eB
    let RA := DA.relabel eA
    let RB := DB.relabel eB
    let D := (RA.contract (TensorSum.pure BB)).add ((TensorSum.pure AA).contract RB)
    refine ⟨D.relabel finSumFinEquiv,?_,?_⟩
    · apply TensorSum.weightLE_relabel
      apply TensorSum.weightLE_add
      · have hh := TensorSum.weightLE_contract (TensorSum.weightLE_relabel hDA eA)
          (TensorSum.weightLE_pure BB (Nat.le_refl BB.expression.weight))
        convert hh using 1
        all_goals try with_reducible_and_instances rfl
        simp only [BB,TensorAtom.relabel,atom_weight,weight]
        omega
      · have hh := TensorSum.weightLE_contract (TensorSum.weightLE_pure AA (Nat.le_refl AA.expression.weight))
          (TensorSum.weightLE_relabel hDB eB)
        convert hh using 1
        all_goals try with_reducible_and_instances rfl
        simp only [AA,TensorAtom.relabel,atom_weight,weight]
        omega
    · exact TensorAtom.HasMaterial.congr
        (TensorAtom.HasMaterial.relabel
          (TensorAtom.HasMaterial.contract (TensorAtom.HasMaterial.relabel hA eA)
            (TensorAtom.HasMaterial.relabel hB eB)) finSumFinEquiv)
        (atom_contract_eval hm hn A B)
  | @adjoint n hn A ih =>
    let : NeZero n := ⟨by omega⟩
    obtain ⟨DA,hDA,hA⟩ := ih
    let e := TensorAtom.lastEquiv (Equiv.refl (Fin n))
    let AA := A.atom.relabel e
    let hcard : 2≤Fintype.card (Fin n) := by simpa using hn
    refine ⟨((DA.relabel e).adjoint hcard).add
      ((TensorSum.pure (AA.insertOne.adjoint hcard)).scale 1 Polynomial.X),?_,?_⟩
    · apply TensorSum.weightLE_add
      · simpa only [weight,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
          TensorSum.weightLE_adjoint hcard (TensorSum.weightLE_relabel hDA e)
      · apply TensorSum.weightLE_scale
        apply TensorSum.weightLE_pure
        rw [TensorAtom.adjoint_weight,TensorAtom.insertOne_weight]
        change A.weight+1≤A.weight+1+2
        omega
    · exact TensorAtom.HasMaterial.congr
        (TensorAtom.HasMaterial.adjoint hcard (TensorAtom.HasMaterial.relabel hA e))
        (atom_adjoint_eval hn A)
end TensorExpression
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal

namespace TensorAtom
variable {S : Type}
theorem hasMaterial (A : TensorAtom S) : ∃B : TensorSum S,
    B.weightLE (A.expression.weight+2) ∧ A.HasMaterial B := by
  obtain ⟨B,hB,h⟩ := A.expression.hasMaterial
  refine ⟨B.relabel A.labels,TensorSum.weightLE_relabel hB A.labels,?_⟩
  exact TensorAtom.HasMaterial.congr (TensorAtom.HasMaterial.relabel h A.labels) (by intros; rfl)
end TensorAtom

namespace TensorSum
variable {S : Type}

lemma combine_eval {I : Type} [Fintype I] (f : I → TensorSum S) {d : ℕ}
    (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : S → Fin d) (p : ℝ × Point d) :
    (combine f).eval F x r L c p=∑i,(f i).eval F x r L c p := by
  change (∑a : (i : I) × (f i).index,((f a.1).term a.2).eval F x r L c p)=_
  rw [Fintype.sum_sigma]
  rfl

def HasMaterial (A B : TensorSum S) : Prop :=
  ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}, Primitive F lam →
    ∀(x : Point d) {r ρ : ℝ}, 0 < r → 0<lam → (lam:ℝ)*r^2≤1/2 → 0≤ρ → ρ<1 →
      ∀(c : S → Fin d) (y : Point d),
        JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
          (A.eval F x r ((lam:ℝ)*r) c) (ρ,y)=B.eval F x r ((lam:ℝ)*r) c (ρ,y)

lemma HasMaterial.pure {A : TensorAtom S} {B : TensorSum S} (h : A.HasMaterial B) :
    (pure A).HasMaterial B := by
  intro d F lam hF x r ρ hr hlam hl h0 h1 c y
  rw [pure_eval]
  exact h hF x hr hlam hl h0 h1 c y

lemma HasMaterial.scale {A B : TensorSum S} (h : A.HasMaterial B) (n : ℕ) (P : Polynomial ℝ) :
    (A.scale n P).HasMaterial ((A.scale n P.derivative).add (B.scale n P)) := by
  intro d F lam hF x r ρ hr hlam hl h0 h1 c y
  have hS := A.timeSmooth hF x hr hlam hl c (ρ,y) (by dsimp; linarith) h1
  have hP := (polynomialTime_smooth (d:=d) P).contDiffAt (x:=(ρ,y))
  have he : (A.scale n P).eval F x r ((lam:ℝ)*r) c=fun p =>
      (r*((lam:ℝ)*r))^n*(P.eval p.1*A.eval F x r ((lam:ℝ)*r) c p) := by
    funext p
    rw [scale_eval]
    ring
  rw [he,JetCalculus.mdir_const_mul_at _ _ _ _ ((hP.mul hS).differentiableAt (by simp)),
    JetCalculus.mdir_mul_at _ _ _ _ (hP.differentiableAt (by simp)) (hS.differentiableAt (by simp)),
    JetCalculus.mdir_time,h hF x hr hlam hl h0 h1,add_eval,scale_eval,scale_eval]
  ring

lemma HasMaterial.combine {I : Type} [Fintype I] {f g : I → TensorSum S}
    (h : ∀i,(f i).HasMaterial (g i)) : (combine f).HasMaterial (combine g) := by
  intro d F lam hF x r ρ hr hlam hl h0 h1 c y
  have he : (TensorSum.combine f).eval F x r ((lam:ℝ)*r) c=fun p => ∑i,(f i).eval F x r ((lam:ℝ)*r) c p :=
    funext (fun p => combine_eval f F x r ((lam:ℝ)*r) c p)
  rw [he,JetCalculus.mdir_sum_at Finset.univ _ _ _ _ (fun i _ =>
    ((f i).timeSmooth hF x hr hlam hl c (ρ,y) (by dsimp; linarith) h1).differentiableAt (by simp)),TensorSum.combine_eval]
  apply Finset.sum_congr rfl
  intro i _
  exact h i hF x hr hlam hl h0 h1 c y

lemma HasMaterial.congr {A A' B : TensorSum S} (h : A.HasMaterial B)
    (he : ∀{d : ℕ} (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : S → Fin d),
      A'.eval F x r L c=A.eval F x r L c) : A'.HasMaterial B := by
  intro d F lam hF x r ρ hr hlam hl h0 h1 c y
  rw [he]
  exact h hF x hr hlam hl h0 h1 c y

theorem hasMaterial (A : TensorSum S) {w : ℕ} (hw : A.weightLE w) :
    ∃B : TensorSum S,B.weightLE (w+2) ∧ A.HasMaterial B := by
  have hf (i : A.index) := (A.term i).atom.hasMaterial
  choose B hB h using hf
  let f : A.index → TensorSum S := fun i => (pure (A.term i).atom).scale (A.term i).power (A.term i).coefficient
  let g : A.index → TensorSum S := fun i =>
    ((pure (A.term i).atom).scale (A.term i).power (A.term i).coefficient.derivative).add
      ((B i).scale (A.term i).power (A.term i).coefficient)
  refine ⟨combine g,?_,?_⟩
  · apply weightLE_combine
    intro i
    apply weightLE_add
    · exact weightLE_scale (weightLE_pure _ ((hw i).trans (by omega))) _ _
    · exact weightLE_scale (weightLE_mono (hB i) (Nat.add_le_add_right (hw i) 2)) _ _
  · have hh : (combine f).HasMaterial (combine g) := HasMaterial.combine (fun i =>
      HasMaterial.scale (HasMaterial.pure (h i)) _ _)
    apply hh.congr
    intro d F x r L c
    funext p
    rw [combine_eval]
    change (∑i,(A.term i).eval F x r L c p)=∑i,(f i).eval F x r L c p
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [f]
    rw [scale_eval,pure_eval]
    rfl
end TensorSum
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace TensorSum
variable {S : Type} [Fintype S] [Nonempty S]

def outer {d : ℕ} (A : TensorSum (S ⊕ Unit)) (F : Point d → ℝ) (x : Point d)
    (r L : ℝ) (c : S → Fin d) : ℝ × Point d → ℝ :=
  JetCalculus.gadj jointSpace (jointScore F x r)
    (fun k => A.eval F x r L (Sum.elim c (fun _ => k)))

end TensorSum
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ScoreAugmented
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators

lemma allSplitBound_pair {d : ℕ} {B : Fin d → Fin d → ℝ} {M : ℝ}
    (hB : Bound B (M^2)) :
    AllSplitBound (fun c : Unit ⊕ Unit → Fin d => B (c (Sum.inl ())) (c (Sum.inr ()))) M := by
  intro I O _ _ _ _ _ _ e
  have hc := Fintype.card_congr e
  simp only [Fintype.card_sum,Fintype.card_unique] at hc
  have hi := Fintype.card_pos (α:=I)
  have ho := Fintype.card_pos (α:=O)
  obtain ⟨uI⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp (show Fintype.card I=1 by omega)
  obtain ⟨uO⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp (show Fintype.card O=1 by omega)
  let : Unique I := uI
  let : Unique O := uO
  cases he0 : e (Sum.inl ()) with
  | inl i =>
    cases he1 : e (Sum.inr ()) with
    | inl j =>
      have hh := e.injective (he0.trans ((congrArg Sum.inl (Subsingleton.elim i j)).trans he1.symm))
      cases hh
    | inr o =>
      have hh := (hB.transpose (sq_nonneg M)).reindex
        (Equiv.funUnique O (Fin d)) (Equiv.funUnique I (Fin d))
      simpa only [he0,he1,Sum.elim_inl,Sum.elim_inr,Equiv.funUnique_apply,
        Subsingleton.elim i (default:I),Subsingleton.elim o (default:O)] using hh
  | inr o =>
    cases he1 : e (Sum.inr ()) with
    | inl i =>
      have hh := hB.reindex (Equiv.funUnique O (Fin d)) (Equiv.funUnique I (Fin d))
      simpa only [he0,he1,Sum.elim_inl,Sum.elim_inr,Equiv.funUnique_apply,
        Subsingleton.elim i (default:I),Subsingleton.elim o (default:O)] using hh
    | inr p =>
      have hh := e.injective (he0.trans ((congrArg Sum.inr (Subsingleton.elim o p)).trans he1.symm))
      cases hh

end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace TensorEnergy

lemma AllSplitBound.add {S : Type} [Fintype S] {d : ℕ}
    {A B : (S → Fin d) → ℝ} {M N : ℝ}
    (hA : AllSplitBound A M) (hB : AllSplitBound B N) (hM : 0≤M) (hN : 0≤N) :
    AllSplitBound (fun c => A c+B c) (M+N) := by
  intro I O _ _ _ _ _ _ e
  exact (hA I O e).add_norm (hB I O e) hM hN

lemma allSplitBound_delta {d : ℕ} : AllSplitBound
    (fun c : Unit ⊕ Unit → Fin d => if c (Sum.inl ())=c (Sum.inr ()) then (1:ℝ) else 0) 1 := by
  have hB : Bound (fun i j : Fin d => if i=j then (1:ℝ) else 0) ((1:ℝ)^2) := by
    intro v
    simp only [one_pow,one_mul,ite_mul,zero_mul]
    simp
  exact @allSplitBound_pair d (fun i j : Fin d => if i=j then (1:ℝ) else 0) 1 hB

lemma allSplitBound_spatial_delta {d : ℕ} {K : Type} [Fintype K]
    (l : List K) (hall : ∀k,k∈l) : AllSplitBound
    (fun c : (K ⊕ Unit) ⊕ Unit → Fin d => if l=[] then
      (if c (Sum.inl (Sum.inr ()))=c (Sum.inr ()) then (1:ℝ) else 0) else 0)
    (if l=[] then 1 else 0) := by
  by_cases hl : l=[]
  · let : IsEmpty K := ⟨fun k => by simpa only [hl,List.not_mem_nil] using hall k⟩
    have hh := (allSplitBound_delta (d:=d)).reindex
      ((Equiv.emptySum K Unit).sumCongr (Equiv.refl Unit)).symm
    simpa only [hl,↓reduceIte,Function.comp_def,Equiv.sumCongr_symm,
      Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,Equiv.refl_symm,Equiv.refl_apply,
      Equiv.emptySum_symm_apply] using hh
  · intro I O _ _ _ _ _ _ e v
    simp [hl]
end TensorEnergy

lemma scoreAugmented_eq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {K : Type} [Fintype K] (l : List K) (hlen : l.length=Fintype.card K)
    (y : Point d) (c : (K ⊕ Unit) ⊕ Unit → Fin d) :
    scoreAugmented (interpolationPotential F x r ρ) l y c =
      (if l=[] then (if c (Sum.inl (Sum.inr ()))=c (Sum.inr ()) then 1 else 0) else 0) +
      (r*ρ)*(ρ^(Fintype.card K+1)*((lam:ℝ)*r))*
        normalizedTensor F x r ρ ((lam:ℝ)*r) y
          (Sum.elim (fun _ => false) (fun _ => true))
          ((l.map Sum.inl++[Sum.inr ()]).map Sum.inl++[Sum.inr ()]) c := by
  let v := EuclideanSpace.basisFun (Fin d) ℝ
  let w := v (c (Sum.inr ()))
  let k := l.map Sum.inl++[Sum.inr ()]
  have hg : directional w (interpolationPotential F x r ρ)=fun y =>
      inner ℝ w y+(r*ρ)*inner ℝ w (conditionalFieldMean F x r ρ y) := by
    funext y
    rw [directional_gradient,interpolationPotential_gradient hF x hr.le hl hρ0 hρ1,
      real_inner_comm,inner_add_right,inner_smul_right]
  have hm := (conditionalFieldMean_component_polySmooth hF x hr hlam hl hρ0 hρ1 (c (Sum.inr ()))).smooth
  have hlin : ContDiff ℝ (⊤:ℕ∞) (fun y => inner ℝ w y) := (innerSL ℝ w).contDiff
  have hklen : k.length=Fintype.card (K ⊕ Unit) := by simp [k,hlen]
  have he : scoreAugmented (interpolationPotential F x r ρ) l y c =
      JetCalculus.jet (fun s => v (c (Sum.inl s))) k
        (directional w (interpolationPotential F x r ρ)) y := by
    simp only [k,JetCalculus.jet_append,JetCalculus.jet_map,JetCalculus.jet]
    rfl
  rw [he,hg,JetCalculus.jet_add hlin (contDiff_const.mul hm),JetCalculus.jet_const_mul hm]
  have hlinear : JetCalculus.jet (fun s => v (c (Sum.inl s))) k
      (fun y => inner ℝ w y) y =
      if l=[] then (if c (Sum.inl (Sum.inr ()))=c (Sum.inr ()) then 1 else 0) else 0 := by
    simp only [k,JetCalculus.jet_append,JetCalculus.jet_map,JetCalculus.jet]
    have hd : JetCalculus.dir (v (c (Sum.inl (Sum.inr ())))) (fun y => inner ℝ w y)=
        fun _ => inner ℝ w (v (c (Sum.inl (Sum.inr ())))) := by
      funext z
      exact congrArg (fun A : Point d →L[ℝ] ℝ => A (v (c (Sum.inl (Sum.inr ())))))
        (innerSL ℝ w).hasFDerivAt.fderiv
    rw [hd,JetCalculus.jet_const]
    by_cases hl : l=[]
    · simp only [hl,↓reduceIte]
      change inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ _) (EuclideanSpace.basisFun (Fin d) ℝ _)=_
      rw [EuclideanSpace.basisFun_inner]
      simp [EuclideanSpace.basisFun_apply,eq_comm]
    · simp only [hl,↓reduceIte]
  dsimp only []
  rw [hlinear]
  have hmean := conditionalFieldMean_jet_normalized hF x hr hlam hl hρ0 hρ1 y k hklen c
  change JetCalculus.jet (fun s => v (c (Sum.inl s))) k
    (fun y => inner ℝ w (conditionalFieldMean F x r ρ y)) y=_ at hmean
  rw [hmean]
  simp only [Fintype.card_sum,Fintype.card_unique]
  ring

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ScoreSlots
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma scoreAugmented_allSplit {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {K : Type} [Fintype K] (l : List K) (hlN : l.Nodup) (hall : ∀k,k∈l) (y : Point d) :
    TensorEnergy.AllSplitBound (scoreAugmented (interpolationPotential F x r ρ) l y)
      ((if l=[] then 1 else 0)+normalizedTensorMajorant (Fintype.card K+2) (1-ρ^2)) := by
  let k : List (K ⊕ Unit) := l.map Sum.inl++[Sum.inr ()]
  have hkN : k.Nodup := by
    simpa using JetCalculus.nodup_sum_append hlN (by simp : ([()] : List Unit).Nodup)
  have hkall : ∀t : K ⊕ Unit,t∈k := by intro t; cases t <;> simp [k,hall]
  have hkkN : (k.map Sum.inl++[Sum.inr ()]).Nodup := by
    simpa using JetCalculus.nodup_sum_append hkN (by simp : ([()] : List Unit).Nodup)
  have hkkall : ∀t : (K ⊕ Unit) ⊕ Unit,t∈k.map Sum.inl++[Sum.inr ()] := by
    intro t; cases t <;> simp [hkall]
  let C := (r*ρ)*(ρ^(Fintype.card K+1)*((lam:ℝ)*r))
  have hC0 : 0≤C := by dsimp [C]; positivity
  have hC1 : C≤1 := by
    have he : C=((lam:ℝ)*r^2)*ρ^(Fintype.card K+2) := by dsimp [C]; rw [pow_succ]; ring
    rw [he]
    have hh := mul_le_of_le_one_right (show (0:ℝ)≤(lam:ℝ)*r^2 by positivity)
      (pow_le_one₀ (n:=Fintype.card K+2) hρ0 hρ1.le)
    linarith
  have hm0 := normalizedTensorMajorant_nonneg (Fintype.card K+2) (1-ρ^2)
  have hN := (normalizedTensor_allSplit hF x hr hlam hl hρ0 hρ1 y
    (Sum.elim (fun _ : K ⊕ Unit => false) (fun _ : Unit => true))
    (k.map Sum.inl++[Sum.inr ()]) hkkN hkkall).const_mul C
  simp only [Fintype.card_sum,Fintype.card_unique,Nat.add_assoc] at hN
  have hNm := hN.mono (mul_nonneg hC0 hm0) (mul_le_of_le_one_left hm0 hC1)
  have hD := TensorEnergy.allSplitBound_spatial_delta (d:=d) l hall
  have he := hD.add hNm (by split_ifs <;> norm_num) hm0
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  funext c
  exact scoreAugmented_eq hF x hr hlam hl hρ0 hρ1 l (list_length_full l hlN hall) y c

lemma scorePosition_allSplit {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (e : ℕ) (y : Point d) :
    TensorEnergy.AllSplitBound (CycleTrace.scorePosition (interpolationPotential F x r ρ)
      (EuclideanSpace.basisFun (Fin d) ℝ) e y)
      ((if e=0 then 1 else 0)+normalizedTensorMajorant (e+2) (1-ρ^2)) := by
  have hh := (scoreAugmented_allSplit hF x hr hlam hl hρ0 hρ1 (List.finRange e)
    (List.nodup_finRange e) (by simp) y).reindex (scoreSlots e)
  have he : (List.finRange e=[] ↔ e=0) := by simp
  have hf : (fun a : Fin (e+2) → Fin d => scoreAugmented (interpolationPotential F x r ρ)
      (List.finRange e) y (a ∘ scoreSlots e))=
      CycleTrace.scorePosition (interpolationPotential F x r ρ) (EuclideanSpace.basisFun (Fin d) ℝ) e y := by
    funext c
    rfl
  rw [hf] at hh
  simpa only [Fintype.card_fin,he] using hh

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

universe u

def extendedSpatial {d : ℕ} {S K : Type u}
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (l : List K) (y : Point d)
    (c : (K ⊕ S) ⊕ Unit → Fin d) : ℝ :=
  spatialTensor F l y (c ∘ (Equiv.sumAssoc K S Unit).symm)

def spatialContractTerm {d : ℕ} {S T K : Type u} (p : K → Prop) [DecidablePred p]
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ) (l : List K) (y : Point d)
    (c : K ⊕ (S ⊕ T) → Fin d) : ℝ :=
  TensorEnergy.singleContract (extendedSpatial F (selectList p l) y)
    (extendedSpatial G (selectList (fun k => ¬p k) l) y) (c ∘ contractSpatialSlots p)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal

lemma scoreSpatial_eq {d h : ℕ} (H : Point d → ℝ) (y : Point d)
    (c : Fin (h+1) ⊕ (Empty ⊕ Unit) → Fin d) :
    scoreAugmented H (List.finRange h) y (c ∘ scoreSpatialSlots h)=
      spatialTensor (scoreField H) (List.finRange (h+1)) y c := by
  unfold scoreAugmented spatialTensor scoreField
  rw [List.finRange_succ_last,JetCalculus.jet_append,JetCalculus.jet_map]
  rfl

lemma scoreField_spatial_allSplit {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (n : ℕ) (hn : 0<n) (y : Point d) :
    TensorEnergy.AllSplitBound (spatialTensor (scoreField (interpolationPotential F x r ρ)) (List.finRange n) y)
      (1+normalizedTensorMajorant (n+1) (1-ρ^2)) := by
  obtain ⟨h,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hh := (scoreAugmented_allSplit hF x hr hlam hl hρ0 hρ1 (List.finRange h)
    (List.nodup_finRange h) (by simp) y).reindex (scoreSpatialSlots h)
  simp only [scoreSpatial_eq,Fintype.card_fin] at hh
  apply hh.mono
  · exact add_nonneg (by split_ifs <;> norm_num) (normalizedTensorMajorant_nonneg _ _)
  · apply add_le_add _ le_rfl
    split_ifs <;> norm_num

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_AnalyticBase
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators

def adjointCommutator {K S : Type} {d : ℕ}
    (H : Point d → ℝ) (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (l : List K)
    (y : Point d) (c : K ⊕ S → Fin d) : ℝ :=
  ∑s∈l.toFinset.powerset.erase ∅,
    spatialContractTerm (fun k => k∈s) (scoreField H) F l y (c ∘ scoreContractSlots K S)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_NormalizedScoreMajorant
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal

def physicalTameScore {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    TameScore (interpolationPotential F x r ρ) (ENNReal.ofReal ((Real.sqrt (1-ρ^2))⁻¹)) where
  bound e := normalizedScoreMajorant e (1-ρ^2)
  nonneg e := normalizedScoreMajorant_nonneg e _
  hessian e y := by
    apply (scorePosition_allSplit hF x hr hlam hl hρ0 hρ1 e y).mono
    · exact add_nonneg (by split_ifs <;> norm_num) (normalizedTensorMajorant_nonneg _ _)
    · dsimp [normalizedScoreMajorant]
      have := normalizedTensorMajorant_nonneg (e+1) (1-ρ^2)
      split_ifs <;> linarith
  spatial e he y := by
    apply (scoreField_spatial_allSplit hF x hr hlam hl hρ0 hρ1 e he y).mono
    · exact add_nonneg (by norm_num) (normalizedTensorMajorant_nonneg _ _)
    · dsimp [normalizedScoreMajorant]
      have := normalizedTensorMajorant_nonneg (e+2) (1-ρ^2)
      linarith
  budget e := by
    have ha : 0<1-ρ^2 := (probability_time hρ0 hρ1).1
    have hh := ENNReal.ofReal_le_ofReal (normalizedScoreMajorant_budget ha (by nlinarith [sq_nonneg ρ]) e)
    have he : ENNReal.ofReal (40*((e:ℝ)+3))=40*((e:ℝ≥0∞)+3) := by
      norm_cast
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by positivity),he,
      ENNReal.ofReal_pow (by positivity)] at hh
    exact hh

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Slice
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory TensorExpression
open scoped Classical BigOperators ENNReal NNReal

namespace TensorAtom
variable {S : Type} [Fintype S]
def slice {d : ℕ} (A : TensorAtom S) (F : Point d → ℝ) (x : Point d) (r ρ L : ℝ) :
    (S → Fin d) → Point d → ℝ := fun c y => A.eval F x r L c (ρ,y)

def spatialBound {d : ℕ} (A : TensorAtom S) (F : Point d → ℝ) (x : Point d)
    (r ρ L : ℝ) (j : ℕ) : Point d → ℝ :=
  spatialEnvelope (A.expression.eval (physicalBase F x r ρ L) (interpolationPotential F x r ρ)) j

end TensorAtom

namespace TensorEnergy
lemma AllSplitBound.abs_const_mul {S : Type} [Fintype S] {d : ℕ}
    {T : (S → Fin d) → ℝ} {M : ℝ} (h : AllSplitBound T M) (c : ℝ) :
    AllSplitBound (fun a => c*T a) (|c| * M) := by
  intro I O _ _ _ _ _ _ e
  convert (h.const_mul c) I O e using 1
  all_goals try with_reducible_and_instances rfl
  simp only [mul_pow,sq_abs]
end TensorEnergy

namespace TensorSum
variable {S : Type} [Fintype S]
def slice {d : ℕ} (A : TensorSum S) (F : Point d → ℝ) (x : Point d) (r ρ L : ℝ) :
    (S → Fin d) → Point d → ℝ := fun c y => A.eval F x r L c (ρ,y)

def spatialBound {d : ℕ} (A : TensorSum S) (F : Point d → ℝ) (x : Point d)
    (r ρ L : ℝ) (j : ℕ) : Point d → ℝ := fun y =>
  ∑i,polynomialBudget (A.term i).coefficient*(A.term i).atom.spatialBound F x r ρ L j y

end TensorSum
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TerminalMean
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set Function Filter MeasureTheory
open scoped NNReal Topology RealInnerProductSpace

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

lemma terminalForward_slice_smooth (t : Icc (0:ℝ) T) :
    ContDiff ℝ (⊤:ℕ∞) (fun y => terminalForward hF x hr.le hl hT0 hT1 (t,y)) :=
  (terminalForward_smooth hF x hr.le hl hT0 hT1).comp (contDiff_const.prodMk contDiff_id)

lemma terminalBackward_slice_smooth (t : Icc (0:ℝ) T) :
    ContDiff ℝ (⊤:ℕ∞) (fun y => terminalBackward hF x hr.le hl hT0 hT1 (t,y)) :=
  (terminalBackward_smooth hF x hr.le hl hT0 hT1).comp (contDiff_const.prodMk contDiff_id)

def terminalHomeomorph (t : Icc (0:ℝ) T) : Point d ≃ₜ Point d where
  toFun := fun y => terminalForward hF x hr.le hl hT0 hT1 (t,y)
  invFun := fun y => terminalBackward hF x hr.le hl hT0 hT1 (t,y)
  left_inv := terminalBackward_forward hF x hr.le hl hT0 hT1 t
  right_inv := terminalForward_backward hF x hr.le hl hT0 hT1 t
  continuous_toFun := (terminalForward_slice_smooth hF x hr hl hT0 hT1 t).continuous
  continuous_invFun := (terminalBackward_slice_smooth hF x hr hl hT0 hT1 t).continuous

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_ForestTensor
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators

theorem AllSplitBound.forest {d n : ℕ} {S : Type} [Fintype S] [Nonempty S]
    (P : Fin n → Type) [∀i,Fintype (P i)] [∀i,Nonempty (P i)]
    {A : (S ⊕ Fin n → Fin d) → ℝ} {B : ∀i,(P i ⊕ Unit → Fin d) → ℝ}
    {M : ℝ} {N : Fin n → ℝ} (hA : AllSplitBound A M) (hB : ∀i,AllSplitBound (B i) (N i)) :
    AllSplitBound (forestTensor P A B) (M*∏i,N i) := by
  induction n generalizing S with
  | zero =>
    let e : S ⊕ (Σi : Fin 0,P i) ≃ S ⊕ Fin 0 :=
      (Equiv.refl S).sumCongr (Equiv.equivOfIsEmpty _ _)
    have hh := hA.reindex e.symm
    have he : forestTensor P A B = fun c => A (c ∘ e.symm) := by
      funext c
      simp only [forestTensor,Fin.prod_univ_zero,mul_one,Fintype.sum_unique]
      congr 1
      funext s
      rcases s with s|i
      · rfl
      · exact Fin.elim0 i
    rw [he,Fin.prod_univ_zero,mul_one]
    exact hh
  | succ n ih =>
    have ha := hA.reindex (forestRoot S)
    have ht := ih (fun i : Fin n => P i.succ) ha (fun i => hB i.succ)
    have hs := ht.reindex (forestShuffle S (Σi : Fin n,P i.succ))
    have hc := (hs.singleContract (hB 0)).reindex (forestOutput S P)
    have he : (M*(∏i : Fin n,N i.succ))*N 0=M*∏i,N i := by
      rw [Fin.prod_univ_succ]; ring
    rw [he] at hc
    convert hc using 1
    all_goals try with_reducible_and_instances rfl
    ext c
    exact forestTensor_succ P A B c
end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators RealInnerProductSpace

theorem AllSplitBound.compAlong {d n : ℕ} (c : OrderedFinpartition n)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Point d) (Point d))
    (B : ∀i,ContinuousMultilinearMap ℝ (fun _ : Fin (c.partSize i) => Point d) (Point d))
    {M : ℝ} {N : Fin c.length → ℝ}
    (hA : AllSplitBound (multilinearTensor A) M)
    (hB : ∀i,AllSplitBound (multilinearTensor (B i)) (N i)) :
    AllSplitBound (multilinearTensor (c.compAlongOrderedFinpartition A B)) (M*∏i,N i) := by
  let (i : Fin c.length) : Nonempty (Fin (c.partSize i)) := Fin.pos_iff_nonempty.mp (c.partSize_pos i)
  have hf := hA.forest (fun i => Fin (c.partSize i))
    (fun i => (hB i).reindex (Equiv.sumComm Unit (Fin (c.partSize i))))
  have hh := hf.reindex ((Equiv.refl Unit).sumCongr c.equivSigma)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext a
  exact multilinearTensor_compAlong c A B a

theorem iteratedFDeriv_comp_allSplit {d n : ℕ} {f g : Point d → Point d} (x : Point d)
    (hf : ContDiffAt ℝ (n:WithTop ℕ∞) f x) (hg : ContDiffAt ℝ (n:WithTop ℕ∞) g (f x))
    (M N : ℕ → ℝ) (hM : ∀k,0≤M k) (hN : ∀k,0≤N k)
    (hG : ∀k≤n,AllSplitBound (multilinearTensor (iteratedFDeriv ℝ k g (f x))) (M k))
    (hF : ∀k≤n,AllSplitBound (multilinearTensor (iteratedFDeriv ℝ k f x)) (N k)) :
    AllSplitBound (multilinearTensor (iteratedFDeriv ℝ n (g ∘ f) x))
      (∑c : OrderedFinpartition n,M c.length * ∏i,N (c.partSize i)) := by
  rw [iteratedFDeriv_comp hg hf (by exact_mod_cast le_rfl)]
  have hh := AllSplitBound.finite_sum
    (fun c : OrderedFinpartition n => mul_nonneg (hM _) (Finset.prod_nonneg (fun i _ => hN _)))
    (fun c : OrderedFinpartition n => (hG c.length c.length_le).compAlong c _ _
      (fun i => hF (c.partSize i) (c.partSize_le i)))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext a
  simp only [FormalMultilinearSeries.taylorComp,multilinearTensor,
    sum_apply,inner_sum,FormalMultilinearSeries.compAlongOrderedFinpartition,ftaylorSeries]
end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace NNReal

lemma multilinearTensor_iterated_mean {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (n : ℕ) (y : Point d) (c : Unit ⊕ Fin n → Fin d) :
    TensorEnergy.multilinearTensor (iteratedFDeriv ℝ n (conditionalFieldMean F x r ρ) y) c=
      ρ^n*((lam:ℝ)*r)*normalizedTensor F x r ρ ((lam:ℝ)*r) y
        (Sum.elim (fun _ => false) (fun _ => true))
        ((List.finRange n).map Sum.inl++[Sum.inr ()]) (c ∘ Equiv.sumComm (Fin n) Unit) := by
  let L := innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl ())))
  have hm := conditionalFieldMean_smooth hF x hr.le hl hρ0 hρ1
  have hh := conditionalFieldMean_jet_normalized hF x hr hlam hl hρ0 hρ1 y
    (List.finRange n) (by simp) (c ∘ Equiv.sumComm (Fin n) Unit)
  change JetCalculus.jet (fun i => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr i)))
    (List.finRange n) (L ∘ conditionalFieldMean F x r ρ) y=_ at hh
  rw [JetCalculus.jet_finRange_eq_iteratedFDeriv (L.contDiff.comp hm)] at hh
  rw [L.iteratedFDeriv_comp_left hm.contDiffAt (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))] at hh
  simpa only [Fintype.card_fin,ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, L,
    innerSL_apply_apply,TensorEnergy.multilinearTensor] using hh

lemma conditionalMean_iterated_allSplit {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    TensorEnergy.AllSplitBound
      (TensorEnergy.multilinearTensor (iteratedFDeriv ℝ n (conditionalFieldMean F x r ρ) y))
      (((lam:ℝ)*r)*normalizedTensorMajorant (n+1) (1-ρ^2)) := by
  have hb := normalizedTensor_allSplit hF x hr hlam hl hρ0 hρ1 y
    (Sum.elim (fun _ : Fin n => false) (fun _ : Unit => true))
    ((List.finRange n).map Sum.inl++[Sum.inr ()])
    (by
      simpa using JetCalculus.nodup_sum_append (List.nodup_finRange n)
        (by simp : ([()] : List Unit).Nodup)) (by intro t; cases t <;> simp)
  have hrb := (hb.reindex (Equiv.sumComm (Fin n) Unit)).const_mul (ρ^n*((lam:ℝ)*r))
  simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_unique] at hrb
  have hh := hrb.mono (mul_nonneg (by positivity) (normalizedTensorMajorant_nonneg _ _)) (show
      ρ^n*((lam:ℝ)*r)*normalizedTensorMajorant (n+1) (1-ρ^2)≤
      ((lam:ℝ)*r)*normalizedTensorMajorant (n+1) (1-ρ^2) by
    rw [mul_assoc]
    exact mul_le_of_le_one_left (mul_nonneg (by positivity) (normalizedTensorMajorant_nonneg _ _))
      (pow_le_one₀ hρ0 hρ1.le))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext c
  exact multilinearTensor_iterated_mean hF x hr hlam hl hρ0 hρ1 n y c
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Squared
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

open TensorEnergy

def spatialSquared {S : Type} [Fintype S] {d : ℕ}
    (F : (S → Fin d) → Point d → ℝ) (j : ℕ) (y : Point d) : ℝ :=
  squared (spatialTensor F (List.finRange j) y)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal
open TensorEnergy

def spatialEnergy {d : ℕ} {S : Type} [Fintype S]
    (F : (S → Fin d) → Point d → ℝ) (j : ℕ) (μ : Measure (Point d)) : ℝ :=
  ∫y,spatialSquared F j y ∂μ

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_SplitBundle
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open Set Function
open scoped BigOperators Classical Matrix.Norms.L2Operator

universe u
variable {S : Type u} [Fintype S] {d : ℕ}

lemma allSplitBound_bundle (T : (S → Fin d) → ℝ) :
    AllSplitBound T ‖splitBundle T‖ := by
  intro I O _ _ _ _ _ _ e
  have h := (bound_norm (splitMatrix T (properOfEquiv e))).mono
    (pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm (splitBundle T) (properOfEquiv e)) 2)
  have h' := h.reindex (Equiv.arrowCongr (rightOfEquiv e) (Equiv.refl (Fin d)))
    (Equiv.arrowCongr (leftOfEquiv e) (Equiv.refl (Fin d)))
  convert h' using 1
  all_goals try with_reducible_and_instances rfl
  ext o i
  unfold splitMatrix
  congr 1
  funext s
  rw [splitEquiv_ofEquiv]
  cases e s <;> simp

lemma bundle_norm_le {T : (S → Fin d) → ℝ} {M : ℝ}
    (hM : 0≤M) (h : AllSplitBound T M) : ‖splitBundle T‖≤M := by
  have hp (p : ProperSplit S) : ‖splitMatrix T p‖≤M := by
    have hh : Bound (splitMatrix T p) (M^2) := h (InSlots p) (OutSlots p) (splitEquiv p)
    exact @Bound.norm_le (OutSlots p → Fin d) (InSlots p → Fin d) _ _ (splitMatrix T p) M hM hh
  exact (pi_norm_le_iff_of_nonneg hM).mpr hp

theorem allSplit_gronwall {T D : ℝ → (S → Fin d) → ℝ} {a b δ K ε : ℝ}
    (hc : ContinuousOn T (Icc a b))
    (hd : ∀t∈Ico a b,HasDerivWithinAt T (D t) (Ici t) t)
    (hδ : 0≤δ) (hε : 0≤ε) (hK : 0≤K)
    (hinit : AllSplitBound (T a) δ)
    (hbound : ∀t∈Ico a b,AllSplitBound (D t) (K*‖splitBundle (T t)‖+ε))
    {t : ℝ} (ht : t∈Icc a b) :
    AllSplitBound (T t) (gronwallBound δ K ε (t-a)) := by
  have hb := norm_le_gronwallBound_of_norm_deriv_right_le
    (splitBundle.continuous.comp_continuousOn hc)
    (fun u hu => splitBundle.hasFDerivAt.comp_hasDerivWithinAt u (hd u hu))
    (bundle_norm_le hδ hinit)
    (fun u hu => bundle_norm_le (by positivity) (hbound u hu)) t ht
  exact (allSplitBound_bundle (T t)).mono
    (norm_nonneg _) hb
end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function
open scoped Classical BigOperators RealInnerProductSpace NNReal

lemma multilinearTensor_iterated_eq_jet {d n : ℕ} {f : Point d → Point d}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (y : Point d) (c : Unit ⊕ Fin n → Fin d) :
    TensorEnergy.multilinearTensor (iteratedFDeriv ℝ n f y) c=
      JetCalculus.jet (fun i => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr i)))
        (List.finRange n) (fun z => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl ()))) (f z)) y := by
  let L := innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl ())))
  change _=JetCalculus.jet _ _ (L ∘ f) y
  rw [JetCalculus.jet_finRange_eq_iteratedFDeriv (L.contDiff.comp hf),
    L.iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,L,
    innerSL_apply_apply,TensorEnergy.multilinearTensor]

lemma spatialTensor_time_deriv {d n : ℕ} {X : ℝ × Point d → Point d}
    (hX : ContDiff ℝ (⊤:ℕ∞) X) (V : Point d → Point d) (t : ℝ)
    (hODE : ∀y,HasDerivAt (fun u => X (u,y)) (V (X (t,y))) t) (y : Point d) :
    HasDerivAt
      (fun u => TensorEnergy.multilinearTensor (iteratedFDeriv ℝ n (fun z => X (u,z)) y))
      (TensorEnergy.multilinearTensor (iteratedFDeriv ℝ n (fun z => V (X (t,z))) y)) t := by
  apply hasDerivAt_pi.mpr
  intro c
  let L := innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl ())))
  let A := L ∘ X
  have hA : ContDiff ℝ (⊤:ℕ∞) A := L.contDiff.comp hX
  have hslice (u : ℝ) : ContDiff ℝ (⊤:ℕ∞) (fun z => X (u,z)) :=
    hX.comp (contDiff_const.prodMk contDiff_id)
  have hd := JetCalculus.time_deriv_spatial_jet hA
    (fun i => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr i))) (List.finRange n) t y
  have he : (fun z => JetCalculus.dir (1,0) A (t,z))=fun z => L (V (X (t,z))) := by
    funext z
    have hleft := ((hA.differentiable (by simp) (t,z)).hasFDerivAt).comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t z))
    exact hleft.unique (L.hasFDerivAt.comp_hasDerivAt t (hODE z))
  rw [he] at hd
  have hm : ContDiff ℝ (⊤:ℕ∞) (fun z => L (V (X (t,z)))) := by
    rw [←he]
    exact (JetCalculus.smooth_dir hA (1,0)).comp (contDiff_const.prodMk contDiff_id)
  have hf : (fun u => TensorEnergy.multilinearTensor (iteratedFDeriv ℝ n (fun z => X (u,z)) y) c)=
      fun u => JetCalculus.jet (fun i => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr i)))
        (List.finRange n) (fun z => L (X (u,z))) y := by
    funext u
    exact multilinearTensor_iterated_eq_jet (hslice u) y c
  rw [hf]

  have hV : ContDiff ℝ (⊤:ℕ∞) (fun z => V (X (t,z))) := by
    have heV : (fun z => V (X (t,z)))=fun z => (fderiv ℝ X (t,z)) (1,0) := by
      funext z
      exact (hODE z).unique (((hX.differentiable (by simp) (t,z)).hasFDerivAt).comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t z)))
    rw [heV]
    exact ((hX.fderiv_right (by simp)).comp (contDiff_const.prodMk contDiff_id)).clm_apply contDiff_const
  rw [multilinearTensor_iterated_eq_jet hV]
  exact hd
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_SpatialTensorContinuous
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Function
open scoped Classical BigOperators RealInnerProductSpace

lemma spatialTensor_continuous {d n : ℕ} {X : ℝ × Point d → Point d}
    (hX : ContDiff ℝ (⊤:ℕ∞) X) (y : Point d) :
    Continuous (fun u => TensorEnergy.multilinearTensor
      (iteratedFDeriv ℝ n (fun z => X (u,z)) y)) := by
  apply continuous_pi
  intro c
  let L := innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl ()) ))
  have hA := L.contDiff.comp hX
  have he : (fun u => TensorEnergy.multilinearTensor (iteratedFDeriv ℝ n (fun z => X (u,z)) y) c)=
      fun u => JetCalculus.jet (fun i : Fin n => (0,EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr i))))
        (List.finRange n) (L ∘ X) (u,y) := by
    funext u
    have hs : ContDiff ℝ (⊤:ℕ∞) (fun z => X (u,z)) := hX.comp (contDiff_const.prodMk contDiff_id)
    rw [multilinearTensor_iterated_eq_jet hs]
    exact congrFun (JetCalculus.jet_right_slice_at (fun z => hA.contDiffAt) _ _) y
  rw [he]
  exact (JetCalculus.smooth_jet hA _ _).continuous.comp (continuous_id.prodMk continuous_const)

namespace TensorEnergy
lemma allSplitBound_subsingleton {S : Type*} [Fintype S] [Subsingleton S]
    {d : ℕ} (A : (S → Fin d) → ℝ) (M : ℝ) : AllSplitBound A M := by
  intro I O _ _ _ _ hi ho e
  obtain ⟨i⟩ := hi
  obtain ⟨o⟩ := ho
  have h := congrArg e (Subsingleton.elim (e.symm (Sum.inl i)) (e.symm (Sum.inr o)))
  simp only [Equiv.apply_symm_apply] at h
  exact (Sum.inl_ne_inr h).elim

lemma allSplitBound_zero {S : Type*} [Fintype S] {d : ℕ} :
    AllSplitBound (fun _ : S → Fin d => (0:ℝ)) 0 := by
  intro I O _ _ _ _ _ _ e v
  simp

lemma multilinearTensor_id_one {d : ℕ} (y : Point d) :
    AllSplitBound (multilinearTensor (iteratedFDeriv ℝ 1 (id : Point d → Point d) y)) 1 := by
  have hh := (allSplitBound_delta (d:=d)).reindex
    ((Equiv.refl Unit).sumCongr (Equiv.ofUnique (Fin 1) Unit)).symm
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext c
  simp [multilinearTensor,EuclideanSpace.basisFun,PiLp.inner_apply,EuclideanSpace.single,
    Equiv.ofUnique]

lemma multilinearTensor_id_bound {d n : ℕ} (y : Point d) :
    AllSplitBound (multilinearTensor (iteratedFDeriv ℝ n (id : Point d → Point d) y)) 1 := by
  cases n with
  | zero =>
    let : Subsingleton (Unit ⊕ Fin 0) := ⟨by intro a b; cases a with
      | inl a => cases b with
        | inl b => rfl
        | inr b => exact Fin.elim0 b
      | inr a => exact Fin.elim0 a⟩
    exact allSplitBound_subsingleton _ _
  | succ n =>
    cases n with
    | zero => exact multilinearTensor_id_one y
    | succ n =>
      rw [show n+1+1=n+2 by omega,multilinearTensor_id_higher]
      exact allSplitBound_zero.mono (by norm_num) (by norm_num)
end TensorEnergy
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_SmoothTensorCurve
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open Set Function
open scoped Classical BigOperators Matrix.Norms.L2Operator

structure SmoothTensorCurve (d : ℕ) (A : ℕ → ℝ) (R b : ℝ)
    (X : ℝ × Point d → Point d) (V : ℝ → Point d → Point d) : Prop where
  smooth : ContDiff ℝ (⊤:ℕ∞) X
  initial : ∀y,X (0,y)=y
  equation : ∀t∈Icc 0 b,∀y,HasDerivAt (fun u => X (u,y)) (V t (X (t,y))) t
  velocity_smooth : ∀t∈Icc 0 b,ContDiff ℝ (⊤:ℕ∞) (V t)
  velocity_bound : ∀n t,t∈Icc 0 b → ∀y,
    AllSplitBound (multilinearTensor (iteratedFDeriv ℝ n (V t) y)) (A n/R^(n-1))

theorem smoothTensorCurve_bounds (A : ℕ → ℝ) (hA : ∀k,0≤A k) (n : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀(d : ℕ) (R b : ℝ) (X : ℝ × Point d → Point d)
      (V : ℝ → Point d → Point d), 0<R → R≤1 → 0≤b → b≤1 →
      SmoothTensorCurve d A R b X V → ∀t∈Icc 0 b,∀y,
      AllSplitBound (multilinearTensor (iteratedFDeriv ℝ n (fun z => X (t,z)) y))
        (C/R^(n-1)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      refine ⟨0,le_rfl,?_⟩
      intro d R b X V hR hR1 hb hb1 hX t ht y
      have he : (fun z => X (t,z))=(fun z => X (t,z)) := rfl
      let : Subsingleton (Unit ⊕ Fin 0) := ⟨by intro a b; cases a with
        | inl a => cases b with
          | inl b => rfl
          | inr b => exact Fin.elim0 b
        | inr a => exact Fin.elim0 a⟩
      exact allSplitBound_subsingleton _ _
    have hn0 : 0<n := Nat.pos_of_ne_zero hn
    choose C hC using fun k (hk : k<n) => ih k hk
    let B (k : ℕ) : ℝ := if hk : k<n then C k hk else 0
    have hB (k : ℕ) : 0≤B k := by
      dsimp [B]
      split_ifs with hk
      · exact (hC k hk).1
      · exact le_rfl
    let F : ℝ := ∑c : OrderedFinpartition n,A c.length*∏i,B (c.partSize i)
    let K : ℝ := (Fintype.card (OrderedFinpartition n):ℝ)*A 1
    have hF : 0≤F := Finset.sum_nonneg (fun c _ => mul_nonneg (hA _) (Finset.prod_nonneg (fun i _ => hB _)))
    have hK : 0≤K := mul_nonneg (Nat.cast_nonneg _) (hA 1)
    have hG := gronwallBound_mono (δ:=1) (by norm_num) hF hK
    have hG0 : 0≤gronwallBound 1 K F 1 := by
      have hh := hG (show (0:ℝ)≤1 by norm_num)
      rw [gronwallBound_x0] at hh
      linarith
    refine ⟨gronwallBound 1 K F 1,hG0,?_⟩
    intro d R b X V hR hR1 hb hb1 hX t ht y
    let T (u : ℝ) := multilinearTensor (iteratedFDeriv ℝ n (fun z => X (u,z)) y)
    let D (u : ℝ) := multilinearTensor (iteratedFDeriv ℝ n (fun z => V u (X (u,z))) y)
    have hpow : 0<R^(n-1) := pow_pos hR _
    have hinit : AllSplitBound (T 0) (1/R^(n-1)) := by
      have he : (fun z => X (0,z))=id := funext hX.initial
      dsimp only [T]
      rw [he]
      exact (multilinearTensor_id_bound y).mono (by norm_num)
        ((le_div_iff₀ hpow).mpr (by simpa using (pow_le_one₀ hR.le hR1 : R^(n-1)≤1)))
    have hd (u : ℝ) (hu : u∈Ico 0 b) : HasDerivWithinAt T (D u) (Ici u) u :=
      (spatialTensor_time_deriv hX.smooth (V u) u (hX.equation u ⟨hu.1,hu.2.le⟩) y).hasDerivWithinAt
    have hbound (u : ℝ) (hu : u∈Ico 0 b) :
        AllSplitBound (D u) (K*‖splitBundle (T u)‖+F/R^(n-1)) := by
      let z := ‖splitBundle (T u)‖
      let N (k : ℕ) : ℝ := if k<n then B k/R^(k-1) else z
      let M (k : ℕ) : ℝ := A k/R^(k-1)
      have hM (k : ℕ) : 0≤M k := div_nonneg (hA _) (pow_nonneg hR.le _)
      have hN (k : ℕ) : 0≤N k := by
        dsimp [N,z]
        split_ifs
        · exact div_nonneg (hB _) (pow_nonneg hR.le _)
        · exact norm_nonneg _
      have hlow (k : ℕ) (hk : k≤n) : AllSplitBound
          (multilinearTensor (iteratedFDeriv ℝ k (fun w => X (u,w)) y)) (N k) := by
        by_cases hkn : k<n
        · have hh := (hC k hkn).2 d R b X V hR hR1 hb hb1 hX u ⟨hu.1,hu.2.le⟩ y
          simpa only [N,B,dite_eq_left hkn,ite_eq_left hkn] using hh
        · have he : k=n := by omega
          subst k
          simpa only [N,lt_self_iff_false,ite_false,z,T] using allSplitBound_bundle (T u)
      have hs : ContDiffAt ℝ (n:ℕ) (fun w => X (u,w)) y :=
        (hX.smooth.comp (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))
      have hv : ContDiffAt ℝ (n:ℕ) (V u) (X (u,y)) :=
        (hX.velocity_smooth u ⟨hu.1,hu.2.le⟩).contDiffAt.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))
      have hh := iteratedFDeriv_comp_allSplit y hs hv M N hM hN
        (fun k hk => hX.velocity_bound k u ⟨hu.1,hu.2.le⟩ (X (u,y))) hlow
      have hp := partition_majorant_linear hM
        (fun k => div_nonneg (hB k) (pow_nonneg hR.le (k-1))) (norm_nonneg (splitBundle (T u)))
        (fun k hk => show N k=B k/R^(k-1) from ite_eq_left hk)
        (show N n=z from ite_eq_right (lt_irrefl n))
      have he : (∑c : OrderedFinpartition n,M c.length*∏i,(B (c.partSize i)/R^(c.partSize i-1)))=
          F/R^(n-1) := partition_sum_scale hn0 A B R
      rw [he] at hp
      have hp' : (∑c : OrderedFinpartition n,M c.length*∏i,N (c.partSize i))≤K*z+F/R^(n-1) := by
        simpa only [M,Nat.sub_self,pow_zero,div_one,K,mul_assoc] using hp
      exact hh.mono (Finset.sum_nonneg (fun c _ => mul_nonneg (hM _) (Finset.prod_nonneg (fun i _ => hN _)))) hp'
    have hg := allSplit_gronwall (spatialTensor_continuous hX.smooth y).continuousOn hd
      (div_nonneg (by norm_num) hpow.le) (div_nonneg hF hpow.le) hK hinit hbound ht
    rw [gronwallBound_div] at hg
    apply hg.mono (div_nonneg (by
      have hh := hG (show (0:ℝ)≤t-0 by linarith [ht.1])
      rw [gronwallBound_x0] at hh
      linarith) hpow.le)
    exact div_le_div_of_nonneg_right (hG (by linarith [ht.2])) hpow.le
end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_NormalizedTensorMajorantScale
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set
open scoped NNReal

lemma conditionalMean_iterated_uniform_split {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ R : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (hR : 0<R) (ha : R^2≤1-ρ^2) (y : Point d) :
    TensorEnergy.AllSplitBound
      (TensorEnergy.multilinearTensor (iteratedFDeriv ℝ n (conditionalFieldMean F x r ρ) y))
      (((lam:ℝ)*r)*normalizedTensorMajorant (n+1) 1/R^(n-1)) := by
  have hb := conditionalMean_iterated_allSplit hF x hr hlam hl hρ0 hρ1 y (n:=n)
  apply hb.mono (mul_nonneg (by positivity) (normalizedTensorMajorant_nonneg _ _))
  have hm := mul_le_mul_of_nonneg_left (normalizedTensorMajorant_scale (n:=n+1) hR ha)
    (show 0≤(lam:ℝ)*r by positivity)
  have he : n+1-2=n-1 := by omega
  simpa only [he,mul_div_assoc] using hm
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_SpatialTransport
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function Filter Metric
open scoped Topology NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

lemma spatialTransport_smooth (s : Icc (0:ℝ) T) :
    ContDiff ℝ (⊤:ℕ∞) (spatialTransport hF x hr hl hT0 hT1 s) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hclip : ContDiff ℝ (⊤:ℕ∞) (smoothTimeClip hT0 hT1) :=
    contDiff_infty.mpr (smoothTimeClip_contDiff hT0 hT1)
  exact (GlobalODE.smooth_flow_joint (smoothProbabilityVelocity_smooth hF x hr hl hT0 hT1)
    (fun u (_ : u∈Icc (-1) (T+1)) => smoothProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
    ⟨s,by constructor <;> linarith [s.2.1,s.2.2]⟩ (smoothTimeClip hT0 hT1 p.1,p.2)
    (smoothTimeClip_mem_extended hT0 hT1 p.1)).comp p
      ((hclip.comp contDiff_fst).prodMk contDiff_snd).contDiffAt

lemma spatialTransport_eq (s t : Icc (0:ℝ) T) (y : Point d) :
    spatialTransport hF x hr hl hT0 hT1 s (t,y)=
      probabilityTransport hF x hr hl hT0 hT1 s t y := by
  rw [probabilityTransport_eq_extended]
  simp only [spatialTransport,smoothTimeClip_eq hT0 hT1 t.2]

lemma spatialTransport_initial (s : Icc (0:ℝ) T) (y : Point d) :
    spatialTransport hF x hr hl hT0 hT1 s (s,y)=y := by
  rw [spatialTransport_eq,probabilityTransport_initial]

lemma spatialTransport_deriv (s : Icc (0:ℝ) T) {t : ℝ} (ht : t∈Icc 0 T) (y : Point d) :
    HasDerivAt (fun u => spatialTransport hF x hr hl hT0 hT1 s (u,y))
      (probabilityVelocity F x r t (spatialTransport hF x hr hl hT0 hT1 s (t,y))) t := by
  have he := smoothTimeClip_eventually_eq hT0 hT1 ht
  have hclip := (hasDerivAt_id t).congr_of_eventuallyEq he
  have hh := GlobalODE.flow_deriv (a:= -1) (b:=T+1)
    (fun u _ => smoothProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
    (smoothProbabilityVelocity_smooth hF x hr hl hT0 hT1).continuous
    ⟨s,by constructor <;> linarith [s.2.1,s.2.2]⟩ y t (by constructor <;> linarith [ht.1,ht.2])
  have hlow : (-1:ℝ)<t := by linarith [ht.1]
  have hhigh : t<T+1 := by linarith [ht.2]
  have hflow := hh.hasDerivAt (Icc_mem_nhds hlow hhigh)
  have hs : smoothTimeClip hT0 hT1 t=t := he.eq_of_nhds
  rw [←hs] at hflow
  have hd := hflow.scomp t hclip
  simp only [hs,smoothProbabilityVelocity,one_smul] at hd
  convert hd using 1 <;> first | rfl | simp only [spatialTransport,hs]
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_MatrixArray
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function
open scoped NNReal BigOperators

lemma probabilityVelocity_iterated_split {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ R : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (hR : 0<R) (ha : R^2≤1-ρ^2) (y : Point d) :
    TensorEnergy.AllSplitBound
      (TensorEnergy.multilinearTensor (iteratedFDeriv ℝ n (probabilityVelocity F x r ρ) y))
      (normalizedTensorMajorant (n+1) 1/R^(n-1)) := by
  have hh := (conditionalMean_iterated_uniform_split hF x hr hlam hl hρ0 hρ1 hR ha y (n:=n)).abs_const_mul (-r)
  rw [←TensorEnergy.multilinearTensor_const_smul (-r) _
    (conditionalFieldMean_smooth hF x hr.le hl hρ0 hρ1)] at hh
  change TensorEnergy.AllSplitBound _ _ at hh
  apply hh.mono (mul_nonneg (abs_nonneg _) (div_nonneg (mul_nonneg (by positivity) (normalizedTensorMajorant_nonneg _ _)) (pow_nonneg hR.le _)))
  rw [abs_neg,abs_of_pos hr]
  have hC := normalizedTensorMajorant_nonneg (n+1) 1
  have he : r*((lam:ℝ)*r*normalizedTensorMajorant (n+1) 1/R^(n-1))=
      ((lam:ℝ)*r^2)*(normalizedTensorMajorant (n+1) 1/R^(n-1)) := by ring
  rw [he]
  exact mul_le_of_le_one_left (by positivity) (by linarith)

theorem probabilityTransport_iterated_split (n : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀(d : ℕ) (F : Point d → ℝ) (lam : ℝ≥0)
      (hF : Primitive F lam) (x : Point d) (r R T : ℝ)
      (hr : 0 < r) (_ : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
      (_ : 0<R) (_ : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1)
      (s t : Icc (0:ℝ) T) (y : Point d),
      TensorEnergy.AllSplitBound
      (TensorEnergy.multilinearTensor (iteratedFDeriv ℝ n
        (probabilityTransport hF x hr.le hl hT0 hT1 s t) y)) (C/R^(n-1)) := by
  obtain ⟨C,hC,hbound⟩ := TensorEnergy.smoothTensorCurve_bounds
    (fun k => normalizedTensorMajorant (k+1) 1)
    (fun k => normalizedTensorMajorant_nonneg _ _) n
  refine ⟨C,hC,?_⟩
  intro d F lam hF x r R T hr hlam hl hR hRT hT0 hT1 s t y
  let a : ℝ := (t:ℝ)-(s:ℝ)
  let q (u : ℝ) := (s:ℝ)+a*u
  have hq (u : ℝ) (hu : u∈Icc (0:ℝ) 1) : q u∈Icc 0 T := by
    dsimp [q,a]
    constructor
    · nlinarith [s.2.1,t.2.1,mul_nonneg s.2.1 (sub_nonneg.mpr hu.2),mul_nonneg t.2.1 hu.1]
    · nlinarith [s.2.2,t.2.2,mul_nonneg (sub_nonneg.mpr s.2.2) (sub_nonneg.mpr hu.2),
        mul_nonneg (sub_nonneg.mpr t.2.2) hu.1]
  have ha : |a|≤1 := (abs_le).mpr ⟨by dsimp [a]; linarith [t.2.1,s.2.2],by dsimp [a]; linarith [t.2.2,s.2.1]⟩
  let X (p : ℝ × Point d) := spatialTransport hF x hr.le hl hT0 hT1 s (q p.1,p.2)
  let V (u : ℝ) (z : Point d) := a • probabilityVelocity F x r (q u) z
  have hVX : TensorEnergy.SmoothTensorCurve d (fun k => normalizedTensorMajorant (k+1) 1) R 1 X V := by
    constructor
    · exact (spatialTransport_smooth hF x hr.le hl hT0 hT1 s).comp
        ((contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd)
    · intro z
      dsimp [X,q]
      simp only [mul_zero,add_zero]
      exact spatialTransport_initial hF x hr.le hl hT0 hT1 s z
    · intro u hu z
      have hd := (spatialTransport_deriv hF x hr.le hl hT0 hT1 s (hq u hu) z).scomp u
        ((hasDerivAt_const u (s:ℝ)).add ((hasDerivAt_const u a).mul (hasDerivAt_id u)))
      simpa only [zero_mul,one_mul,mul_one,zero_add,X,V,q,Function.comp_def] using hd
    · intro u hu
      exact (contDiff_const (c:=a)).smul ((contDiff_const (c:=(-r:ℝ))).smul
        (conditionalFieldMean_smooth hF x hr.le hl (hq u hu).1 ((hq u hu).2.trans_lt hT1)))
    · intro k u hu z
      have huT := hq u hu
      have hρ : R^2≤1-(q u)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr huT.2) (add_nonneg hT0 huT.1)]
      have hh := (probabilityVelocity_iterated_split hF x hr hlam hl huT.1
        (huT.2.trans_lt hT1) hR hρ z (n:=k)).abs_const_mul a
      have hvs : ContDiff ℝ (⊤:ℕ∞) (probabilityVelocity F x r (q u)) :=
        (contDiff_const (c:=(-r:ℝ))).smul (conditionalFieldMean_smooth hF x hr.le hl huT.1 (huT.2.trans_lt hT1))
      rw [←TensorEnergy.multilinearTensor_const_smul a (probabilityVelocity F x r (q u)) hvs z] at hh
      apply hh.mono (mul_nonneg (abs_nonneg _) (div_nonneg (normalizedTensorMajorant_nonneg _ _) (pow_nonneg hR.le _)))
      exact mul_le_of_le_one_left (div_nonneg (normalizedTensorMajorant_nonneg _ _) (pow_nonneg hR.le _)) ha
  have hR1 : R≤1 := by nlinarith [sq_nonneg T]
  have hh := hbound d R 1 X V hR hR1 (by norm_num) le_rfl hVX 1 ⟨by norm_num,le_rfl⟩ y
  have he : (fun z => X (1,z))=probabilityTransport hF x hr.le hl hT0 hT1 s t := by
    funext z
    dsimp [X,q,a]
    rw [mul_one,add_sub_cancel]
    exact spatialTransport_eq hF x hr.le hl hT0 hT1 s t z
  rwa [he] at hh
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TransportMajorant
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function
open scoped NNReal BigOperators
open TensorEnergy

def transportMajorant (n : ℕ) : ℝ := (probabilityTransport_iterated_split n).choose

def jacobianMajorant (n : ℕ) : ℝ :=
  ∑c : OrderedFinpartition n,transportMajorant (c.length+1)*∏i,transportMajorant (c.partSize i)
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ComposedJetMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function
open scoped Classical NNReal BigOperators
open TensorEnergy

def composedJetMajorant (n : ℕ) : ℝ :=
  ∑c : OrderedFinpartition n,normalizedTensorMajorant (c.length+2) 1*∏i,transportMajorant (c.partSize i)

def kernelMajorant (n : ℕ) : ℝ :=
  ∑s∈(Finset.univ : Finset (Fin n)).powerset,jacobianMajorant s.card*composedJetMajorant (n-s.card)
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_FlowJetMajorant
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open Set Function
open scoped Classical BigOperators RealInnerProductSpace

def flowJetMajorant (A : ℕ → ℝ) (hA : ∀k,0≤A k) (n : ℕ) : ℝ :=
  (smoothTensorCurve_bounds A hA n).choose

def flowCorrectionMajorant (A : ℕ → ℝ) (hA : ∀k,0≤A k) (n : ℕ) : ℝ :=
  ∑c : OrderedFinpartition n,A c.length*∏i,flowJetMajorant A hA (c.partSize i)
end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TransportCorrectionMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function TensorEnergy
open scoped NNReal BigOperators

def transportCorrectionMajorant (n : ℕ) : ℝ := flowCorrectionMajorant
  (fun k => normalizedTensorMajorant (k+1) 1) (fun _ => normalizedTensorMajorant_nonneg _ _) n
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_CenteringStateBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

def centeringStateBudget (n : ℕ) : ℝ :=
  iterEnergyBudget harmonicGradientBound (fun k => 2*kernelMajorant k)
    (fun k => 2+normalizedTensorMajorant (k+1) 1) (fun _ => 1) n 0

def centeringMeanBudget (n : ℕ) : ℝ :=
  iterEnergyBudget harmonicGradientBound (fun k => 2*kernelMajorant k)
    (fun k => 2+normalizedTensorMajorant (k+1) 1)
    (fun k => (normalizedTensorMajorant (k+1) 1)^2) n 0

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_HarmonicCorrectionBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy Quadrature

def harmonicCorrectionBudget (n : ℕ) : ℝ :=
  iterEnergyBudget harmonicGradientBound (fun _ => 2)
    (fun k => 2+normalizedTensorMajorant (k+1) 1)
    (fun k => (transportCorrectionMajorant k)^2) n 0

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_MeanMaterialVector
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory Set ProbabilityTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

def meanMaterialVector {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ) (n : ℕ)
    (p : ℝ × Point d) : Point d :=
  WithLp.toLp 2 (fun i => JetCalculus.materialIter (1,0) jointSpace r (jointMean F x r) n
    (jointMean F x r i) p)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

def meanPathJet {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (T : ℝ) (n : ℕ) (t : ℝ) (z : Point d) : Point d :=
  meanMaterialVector F x r n (probabilityTimeClamp T t,
    fullProbabilityFlow hF x hr hl (probabilityTimeClamp T t) z)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_SingleCellBasisBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators

def singleCellBasisBudget (n : ℕ) : ℝ :=
  Classical.choose (exists_basis_budget (probabilityNodes n))

lemma singleCellBasisBudget_spec (n : ℕ) :
    1 ≤ singleCellBasisBudget n ∧
      ∀v∈Icc (0:ℝ) 1,∑i,|basis (probabilityNodes n) i v| ≤ singleCellBasisBudget n :=
  Classical.choose_spec (exists_basis_budget (probabilityNodes n))

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_HarmonicStationaryMoment
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

def meanCellResidual {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (n : ℕ) (a b θ : ℝ) (z : Point d) : Point d :=
  ∫t in 0..θ,meanPathJet hF x hr hl b 0 (a+(b-a)*t) z-
    interpolation (probabilityNodes n)
      (fun i => meanPathJet hF x hr hl b 0 (a+(b-a)*probabilityNodes n i) z) t

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

def probabilityMeanDefect {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (T h : ℝ) (n : ℕ) (i : ProbabilityNode T h n) (z : Point d) : Point d :=
  (∫t in 0..probabilityNodeTime T h n i,meanPathJet hF x hr hl T 0 t z)-
    ∑j,probabilityWeight T h n i j • meanPathJet hF x hr hl T 0 (probabilityNodeTime T h n j) z

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_KernelActionRmsBudget
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

def kernelActionRmsBudget {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (lam Ap Ah Lp : ℝ≥0) (r R ρ h ψ C J : ℝ) (k n m N : ℕ) : ℝ :=
  2*((∑i,|derivativeWeight (angleNodes m) i/ψ|)*
    (∑i,|derivativeWeight (angleNodes m) i/ψ| *
      kernelValueRmsBudget F x lam Ap Ah Lp r R ρ h (ψ*angleNodes m i) C J k n N))+
  2*(((∑i,|derivativeWeight (angleNodes m) i|)/ψ)^2*
    (((ψ*m)^(m+1)/(m.factorial:ℝ))^2*
      ((d*((lam:ℝ)*r^2)^2)*(R⁻¹)^(4*(m+1))*harmonicCorrectionBudget (m+1))))

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_ArrayMatrix
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set Filter MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace TensorSum

def matrixEval {d : ℕ} (A : TensorSum (Unit ⊕ Unit)) (F : Point d → ℝ)
    (x : Point d) (r L : ℝ) (p : ℝ × Point d) : Point d →L[ℝ] Point d :=
  TensorEnergy.arrayMatrix (fun c => A.eval F x r L c p)

end TensorSum

namespace TensorSum

def material {S : Type} (A : TensorSum S) {w : ℕ} (hw : A.weightLE w) : TensorSum S :=
  Classical.choose (A.hasMaterial hw)
lemma material_weight {S : Type} (A : TensorSum S) {w : ℕ} (hw : A.weightLE w) :
    (A.material hw).weightLE (w+2) := (Classical.choose_spec (A.hasMaterial hw)).1

def terminalQ : (n : ℕ) → {A : TensorSum (Unit ⊕ Unit) // A.weightLE (2*n)}
  | 0 => ⟨firstMatrix.scale 0 Polynomial.X,weightLE_scale firstMatrix_weight _ _⟩
  | n+1 =>
    let Q := terminalQ n
    ⟨((firstMatrix.matrixComp Q.val).scale 1 Polynomial.X).add (Q.val.material Q.property),
      weightLE_add
        (weightLE_mono (weightLE_scale (matrixComp_weight firstMatrix_weight Q.property) _ _)
          (by omega))
        (weightLE_mono (Q.val.material_weight Q.property) (by omega))⟩

end TensorSum

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_TerminalDerivativeBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

def terminalDerivativeBudget (n d : ℕ) (lam : ℝ≥0) (r : ℝ) : ℝ :=
  (r*((lam:ℝ)*r)*Real.exp (Real.pi^2/4))*
    ((TensorSum.terminalQ n).val.momentBudget d 0 2).toReal

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_KernelAnalyticBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

def kernelAnalyticBudget (n d : ℕ) (lam : ℝ≥0) (r T h D : ℝ) : ℝ :=
  32*(1+D^2+(∑i,|zeroHermiteWeight (probabilityNodes (n+1)) 0 i|)^2)*
    (2*logMeshLength T*terminalDerivativeBudget (n+1) d lam r*2^(n+1)*h^n)^2*d

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_StationaryPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature TensorEnergy
open scoped Classical BigOperators NNReal

def centeringRowBudget (n : ℕ) : ℝ≥0 :=
  ⟨(n+1)*singleCellBasisBudget n,by positivity [(singleCellBasisBudget_spec n).1]⟩

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_CenteringStateQuadratureBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature TensorEnergy
open scoped Classical BigOperators NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r R T s : ℝ}
  (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2 ≤ 1/2)
  (hR : 0<R) (hRT : R^2 ≤ 1-T^2) (hT0 : 0 ≤ T) (hT1 : T<1) (hs : 0 < s)
  (X : StationaryPath (gibbs (centeringPotential F x r T))
    (skewLieField (centeringPotential F x r T) (jointSkew (centeringKernel hF x hr hl hT0 hT1) s)))

def centeringStateQuadratureBudget (n d : ℕ) (lam : ℝ≥0) (r R s : ℝ) : ℝ :=
  4*(singleCellBasisBudget n)^2*
    (((d+d:ℕ):ℝ)*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+2)*centeringStateBudget (n+2))

def centeringMeanQuadratureBudget (n d : ℕ) (lam : ℝ≥0) (r R s : ℝ) : ℝ :=
  4*(singleCellBasisBudget n)^2*
    ((d*((lam:ℝ)*r)^2)*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+1)*centeringMeanBudget (n+1))

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_CenteringMeanCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators NNReal

def centeringInitialBudget (d : ℕ) (lam : ℝ≥0) (r R s : ℝ) : ℝ :=
  (((d+d:ℕ):ℝ)*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)*centeringStateBudget 1)

def centeringPicardBudget (nc Nc d : ℕ) (lam K : ℝ≥0) (r R s Bv : ℝ) : ℝ :=
  (2*Real.sqrt (2*(centeringRowBudget nc:ℝ)^2*Bv+
      2*centeringStateQuadratureBudget nc d lam r R s)+
    ((centeringRowBudget nc*K:ℝ≥0):ℝ)^Nc*Real.sqrt (centeringInitialBudget d lam r R s))^2

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_KernelActionNormalizedBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators NNReal

def kernelActionNormalizedBudget (d k n m N : ℕ) (lam Ap Ah Lp : ℝ≥0)
    (r R h ψ C J : ℝ) : ℝ :=
  let S := (∑i,|derivativeWeight (angleNodes m) i|)/ψ
  let V := (numericalContractionCoefficient Ap Ah Lp+1)*numericalErrorCoefficient C J
  let B := kernelNormalizedTerm d k n N lam Ap Ah Lp r R h (ψ*m)
  600*(V*S*B)^2+2*S^2*((ψ*m)^(m+1)/(m.factorial:ℝ))^2*
    (R⁻¹)^(4*(m+1))*harmonicCorrectionBudget (m+1)

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_KernelAnalyticNormalizedBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators NNReal

def kernelAnalyticNormalizedBudget (n d : ℕ) (T h D : ℝ) : ℝ :=
  32*(1+D^2+(∑i,|zeroHermiteWeight (probabilityNodes (n+1)) 0 i|)^2)*
    (2*logMeshLength T*(Real.exp (Real.pi^2/4)*(TensorSum.terminalQ (n+1)).val.logCoefficient 0 2)*
      (1+Real.log ((d:ℝ)+1))^((TensorSum.terminalQ (n+1)).val.logDegree 0)*2^(n+1)*h^n)^2

def velocityNormalizedBudget (d k n m N : ℕ) (lam Ap Ah Lp : ℝ≥0)
    (r R T h ψ C J D : ℝ) : ℝ :=
  2*(∑v,|terminalQuadratureWeight T h n v|)^2*
    kernelActionNormalizedBudget d k (n+1) m N lam Ap Ah Lp r R h ψ C J+
      2*kernelAnalyticNormalizedBudget n d T h D

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators NNReal

def centerStateQuadratureEnvelope (n : ℕ) (α R : ℝ) : ℝ :=
  8*(singleCellBasisBudget n)^2*(α^2*(R⁻¹)^4)^(n+2)*centeringStateBudget (n+2)
def centerInitialEnvelope (α R : ℝ) : ℝ :=
  2*(α^2*(R⁻¹)^4)*centeringStateBudget 1

def centerStateEnvelope (n N : ℕ) (α R q E : ℝ) : ℝ :=
  8*(2*(centeringRowBudget n:ℝ)^2*α^2*E+2*centerStateQuadratureEnvelope n α R)+
    2*q^(2*N)*centerInitialEnvelope α R

def centerMeanEnvelope (n : ℕ) (α R Z : ℝ) : ℝ :=
  2*(centeringRowBudget n:ℝ)^2*(Real.pi^2/2)^2*α^2*Z+
    8*(singleCellBasisBudget n)^2*α^2*(α^2*(R⁻¹)^4)^(n+1)*centeringMeanBudget (n+1)

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_TranscriptRejection
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling

def finiteRejectionAlgorithm (d q : ℕ) : OracleAlgorithm (Fin q → Point d × ℝ) d q where
  query i p := (p.1 i).1
  query_measurable _ := by fun_prop
  output p := transcriptRejection q (p.1,fun i => (p.2 i).1)
  output_measurable := (measurable_transcriptRejection d q).comp (measurable_fst.prodMk
    (Measurable.of_eval fun _ => by fun_prop))

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_PairGauge
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeanTree MeasureTheory ProbabilityTheory
open scoped Classical NNReal

variable {d : ℕ}

def pairGauge (C : ℝ) (z : Point d × Point d) : ℝ := 1+C+‖z‖
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_NumericalScalars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter Quadrature
open scoped Classical NNReal

def centeringCalibrationGood (d k n N : ℕ) (A Ap Ah Lp contraction : ℝ≥0)
    (C J₀ D κ J t w : ℝ) (v : NumericalScalars) : Prop :=
  let R := (d:ℝ)^(-(κ*t))
  let T := sourceCorrelation (κ*t) d
  let h := (d:ℝ)^(-(κ*w))
  let ψ := (d:ℝ)^(-(κ*(4*t)))
  let E := velocityNormalizedBudget d k n n N v.lam Ap Ah Lp v.r R T h ψ C J₀ D
  let q := centeringRowBudget n*velocityJointLip n n A v.lam v.r T h ψ v.s
  let Z := centerStateEnvelope n N ((v.lam:ℝ)*v.r/v.s) R (q:ℝ) E
  (v.lam:ℝ)*v.r^2≤1/2 ∧ contraction*probabilityMeanLipschitz v.lam v.r≤1/2 ∧
    q≤1/2 ∧ Z≤(d:ℝ)^(-(2*κ*J)) ∧
    centerMeanEnvelope n ((v.lam:ℝ)*v.r/v.s) R Z≤(d:ℝ)^(-(2*κ*J))

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_PrependTape
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory OracleCompiler Function
open scoped Classical

variable {d : ℕ}

def prependTape (k : ℕ) (z : Point d × (Fin k → Point d)) : Fin (1+k) → Point d :=
  Fin.append (fun _ => z.1) z.2

def meanTape (c k : ℕ) (z : (Fin c → Point d) × (Point d × (Fin k → Point d))) :
    Fin (c+(1+k)) → Point d := Fin.append z.1 (prependTape k z.2)

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_NoiseKernel
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical ENNReal

variable {d : ℕ}

instance noiseKernel_markov (s : ℝ) : IsMarkovKernel (noiseKernel (d:=d) s) := by
  unfold noiseKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

def proximalKernel (V : Point d → ℝ) (hV : Admissible V) (h : ℝ) : Kernel (Point d) (Point d) :=
  noiseKernel (Real.sqrt h) ∘ₖ posteriorKernel V hV h

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical ENNReal

variable {d : ℕ}

def halvingKernel (V : Point d → ℝ) (hV : Admissible V) (h : ℝ) : Kernel (Point d) (Point d) :=
  (Kernel.id ×ₖ proximalKernel V hV h).map (fun p => (1/2:ℝ) • (p.1+p.2))

end LogConcaveSampling

end

end

end OAI
end


