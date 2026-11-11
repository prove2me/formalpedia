-- Prove2me | Definitions.Def_Q238K027
-- name    : Q238K027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:21:00.146335+00:00
-- url     : https://prove2.me/theorems/db187c32-ae91-4eb4-b56c-235521273438
-- title:
--   Definitions bundle Q238K027 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 40 declarations of OpenAI's Lean: 36 definitions, 3 inductive types or structures and 1 theorem. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRefine.ctxBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryResolve.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinarySensitive.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.pack`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Outcome.Keys`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Outcome.Resources`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Outcome.Rooted`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Output.Correct`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Output.Resources`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Output.project`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.StartOutput.Correct`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.StartOutput.Rooted`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.StartOutput.project`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.State.Resources`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.State.b`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.advanceState`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.finish`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.initial`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.initialCount`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.initialHistory`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.leafState`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.resolve`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.sameState`, `OAI.MetricKMedianRecovery.CanonicalSensitiveEndpoint.EndpointSpec`, `OAI.MetricKMedianRecovery.CanonicalSensitiveEndpoint.run`, `OAI.MetricKMedianRecovery.RationalLeaves.BankBound`, `OAI.MetricKMedianRecovery.Sampling.Comparison.blueDestination`, `OAI.MetricKMedianRecovery.Sampling.Comparison.designatedDestination`, `OAI.MetricKMedianRecovery.Sampling.Comparison.endpointCharge`, `OAI.MetricKMedianRecovery.Sampling.Comparison.guideKernel`, `OAI.MetricKMedianRecovery.Sampling.Comparison.guideLoss`, `OAI.MetricKMedianRecovery.Sampling.Comparison.guidedUpdate`, `OAI.MetricKMedianRecovery.Sampling.Comparison.history`, `OAI.MetricKMedianRecovery.Sampling.Comparison.integralActions`, `OAI.MetricKMedianRecovery.Sampling.Comparison.stop`, `OAI.MetricKMedianRecovery.Sampling.Comparison.stoppedActual`, `OAI.MetricKMedianRecovery.Sampling.Precision.Good`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_IntegralPrecision`, `KMedianRecovery_Branching_CopyAge`, `KMedianRecovery_Branching_ObservableCapacity`, `KMedianRecovery_Machines_CorrectionSize`, `KMedianRecovery_Machines_MergeResources`, `KMedianRecovery_Machines_RefineMachine`, `KMedianRecovery_Machines_ResolveMachine`, `KMedianRecovery_Machines_SensitiveMachine`, `KMedianRecovery_Recovery_BlindUpdate`, `KMedianRecovery_Recovery_CanonicalParents`, `KMedianRecovery_Recovery_CoupledFinish`, `KMedianRecovery_Recovery_CoupledInitial`, `KMedianRecovery_Recovery_CoupledLeaf`, `KMedianRecovery_Recovery_CoupledResolve`, `KMedianRecovery_Recovery_DestinationFacility`, `KMedianRecovery_Recovery_Destinations`, `KMedianRecovery_Recovery_Guide`, `KMedianRecovery_Recovery_InitialProject`, `KMedianRecovery_Recovery_LeafOrder`, `KMedianRecovery_Recovery_LengthSearch`, `KMedianRecovery_Recovery_NearEligible`, `KMedianRecovery_Recovery_Values`, `KMedianRecovery_Strictness_SurplusPostprocess`.
--
--   **Imports.** It imports the bundles `Q238K017`, `Q238K018`, `Q238K020`, `Q238K021` and `Q238K022` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q238K031`; the statements `OAI_MetricKMedianRecovery_BitMachine_BinaryBranchContext_classOf_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.favorable_literal_plan_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.planned_successful_completion_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.extract_output_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.fair_color_label_completion_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.successful_probability_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.coefficient_source_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.sumWords_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.summand_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.prepared_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.rowCoefficients_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.rowWord_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRefine.cutOp_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.integral_spec_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.localInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.check_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.completion_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.fair_zero_completion_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.successful_completion_s238`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.initialHistory_spec_s238`, `OAI.MetricKMedianRecovery.CanonicalSensitiveEndpoint.endpoints_s238`, `OAI.MetricKMedianRecovery.Sampling.Comparison.guideLoss_domination_s238`, `OAI.MetricKMedianRecovery.Sampling.Comparison.history_menu_budget_s238` and `OAI.MetricKMedianRecovery.Sampling.Comparison.integral_records_success_s238`; the proofs of `OAI_MetricKMedianRecovery_BitMachine_BinaryBranchContext_classOf_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.favorable_literal_plan_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.planned_successful_completion_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryCategorical_choices_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryDecision_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.extract_output_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output_success_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.fair_color_label_completion_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.successful_probability_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.coefficient_source_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryOpeningConstant_constant_source_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.sumWords_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.summand_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.bids_context_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate.updatedBudget_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.prepared_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.rowCoefficients_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.rowWord_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.result_success_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRefine.cutOp_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.integral_spec_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.localInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.check_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.completion_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.fair_zero_completion_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.successful_completion_s238`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.initialHistory_spec_s238`, `OAI.MetricKMedianRecovery.CanonicalSensitiveEndpoint.endpoints_s238`, `OAI.MetricKMedianRecovery.Sampling.Comparison.guideLoss_domination_s238`, `OAI.MetricKMedianRecovery.Sampling.Comparison.history_menu_budget_s238`, `OAI.MetricKMedianRecovery.Sampling.Comparison.integralPrecision_spec_s238`, `OAI.MetricKMedianRecovery.Sampling.Comparison.integral_records_success_s238` and `OAI.MetricKMedianRecovery.Sampling.Comparison.surrogate_success_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_Q238K017
import Definitions.Def_Q238K018
import Definitions.Def_Q238K020
import Definitions.Def_Q238K021
import Definitions.Def_Q238K022

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Destinations
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

noncomputable def endpointCharge (C : Comparison D S O) (Δ : ℝ) (s : State V)
    (theta : ℝ) (J : Finset V) (p : V) : ℝ :=
  if C.assign p ∈ C.good then dist p (C.proxy (C.assign p))
  else if C.assign p ∈ C.covered s then
    dist p (C.assign p) + theta *
      (dist (C.leaderPair s (C.assign p)).1 (C.assign p) + (C.leaderPair s (C.assign p)).2)
  else if p ∈ J then dist p (C.assign p) else reference S Δ s p

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DestinationFacility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

noncomputable def designatedDestination (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) (v : V) : Destination V s.leaves.length :=
  selectedDestination theta (C.coveredCenter s) (leafCenter s) (leafRadius s)
    (C.destinations s) (C.destinations_nonempty hD s) v

noncomputable def blueDestination (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) (u : V) : V :=
  destinationFacility (C.coveredCenter s) (C.designatedDestination hD s theta u)

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NearEligible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
namespace Comparison
variable {D S O : Finset V}
open RadiusMenus

open scoped Classical

noncomputable def stop (C : Comparison D S O) (hD : D.Nonempty) (Δ : ℝ) : Option (State V) → Prop
  | none => False
  | some s => C.Correct hD mainKappa s ∧ C.Terminal mainKappa Δ s

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Guide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
namespace Comparison
variable {D S O : Finset V}
open RadiusMenus
open scoped Classical

noncomputable def guideKernel (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card) :
    Guided.Kernel (Option (State V)) (MainAction D C.bad.card) :=
  ⟨fun s a => (C.guideAt hD Δ hΔ hP hm s).weight () a,
    fun s a => (C.guideAt hD Δ hΔ hP hm s).nonneg () a,
    fun s => (C.guideAt hD Δ hΔ hP hm s).total ()⟩

noncomputable def stoppedActual (C : Comparison D S O) (hD : D.Nonempty) (Δ : ℝ) :=
  Guided.stoppedKernel (mainActual D S Δ C.bad.card) (C.stop hD Δ) (.inl ())

noncomputable def guidedUpdate (C : Comparison D S O) (hD : D.Nonempty) (F : Finset V) (Δ : ℝ) :=
  Guided.stoppedUpdate
    (update D F S hD Δ (comparisonCost D C.assign) mainKappa C.bad.card
      (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa C.bad.card))
    (C.stop hD Δ)

noncomputable def guideLoss (C : Comparison D S O) (hD : D.Nonempty) (Δ : ℝ)
    (s : Option (State V)) (a : MainAction D C.bad.card) : ℝ :=
  if C.Valid hD s ∧ ¬C.stop hD Δ s then
    NearClients.progressConstant mainKappa * actionMenuWeight C.bad.card a else 1

noncomputable def history (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (Δ : ℝ) (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (i : Fin (n+1)) : State V :=
  (Guided.states (C.guidedUpdate hD F Δ) n (some State.initial) seed i).getD State.initial

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BlindUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Precision
open RadiusMenus Guided FixedDyadic FiniteSampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

def Good (s : Option (State V)) : Prop :=
  ∀ t, s = some t → ∀ z ∈ t.leaves, (1:ℝ) ≤ z.2

end MetricKMedianRecovery.Sampling.Precision

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralPrecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open MetricKMedianRecovery RadiusMenus Guided FixedDyadic FiniteSampling Precision
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

attribute [local instance] OAI.MetricKMedianRecovery.Sampling.Comparison.instDecidableEqAction_2
noncomputable def integralActions (D F S : Finset V) (hD : D.Nonempty)
    (Δ P : ℝ) (m : ℕ) (bits : IntegralBits D Δ m) : Fin (2*m) → MainAction D m :=
  actions (blindUpdate D F S hD Δ P m) (mainActual D S Δ m)
    (integralPrecision D Δ m) (Sum.inl ()) (2*m) (some State.initial) bits

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthSearch
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalSensitiveEndpoint
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing CanonicalLengthView RationalLeaves
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

def EndpointSpec (loc : Fin d → V) (F : Finset V) (B Q : Finset (Label V))
    (v lam eta : ℝ) (q n k key : ℕ) (b : ℚ) (H : List (Label V))
    (T U : List (List (Label V))) (J : Plan (Label V)) : Prop :=
  let C := J.common H
  let i := parent J.root
  Good (fun j=>original (loc j)) (F.image original) B Q v ((1+v^2)^q) lam eta C ∧
  Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i 0) B)
    (insert (leaf key i 0) (Q∪C.toFinset)) v lam (q+1) n (J.small T U) ∧
  Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i b) B)
    (insert (leaf key i b) (Q∪C.toFinset)) v lam (q+1) n (J.large T U) ∧
  let a := ((after (insert (leaf key i 0) (Q∪C.toFinset)) (J.small T U))∩F.image original).card
  let c := ((after (insert (leaf key i b) (Q∪C.toFinset)) (J.large T U))∩F.image original).card
  a=k ∨ Sandwich k a c

end MetricKMedianRecovery.CanonicalSensitiveEndpoint

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LeafOrder
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalSensitiveEndpoint
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing CanonicalLengthView RationalLeaves
variable {V : Type*} [LinearOrder V] {d : ℕ}

def run (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (Q : Finset (Label V)) (v lam b : ℚ) (q n k key precision : ℕ)
    (H : List (Label V)) (T U : List (List (Label V))) (J : Plan (Label V)) :
    CanonicalLengthSearch.Result (Label V) :=
  let C := J.common H
  let i := parent J.root
  let A := J.small T U
  let Z := J.large T U
  let R := Q∪C.toFinset
  if ((after (insert (leaf key i 0) R) A)∩F.image original).card=k then
    .success 0 A
  else
    CanonicalLengthSearch.run (F.image original) R (leaf key i)
      (fun s=>FiniteLabelContinuation.continuation (fun j=>original (loc j)) (rows distance)
        (F.image original) v lam (q+1) n (insert (leaf key i s) R)) A Z b k precision

attribute [local instance] RationalLeaves.metric

end MetricKMedianRecovery.CanonicalSensitiveEndpoint

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [DecidableEq V] {d : ℕ}

def State.b (F : Finset V) (s : State V) :=
  ((after (after ∅ s.P) s.U)∩F.image original).card

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

def Output.Correct (loc : Fin d → V) (F : Finset V) (v eta lo hi : ℝ)
    (total k : ℕ) (o : Output V) : Prop :=
  Disjoint (F.image original) o.B ∧ lo≤(o.lam:ℝ) ∧ (o.lam:ℝ)≤hi ∧
  PrefixData (fun j=>original (loc j)) (F.image original) o.B v o.lam eta total o.P ∧
    ((after ∅ o.P)∩F.image original).card=k

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MergeResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
open RationalHeight
variable {V : Type*} [DecidableEq V]

structure BankBound (F : Finset V) (h key size : ℕ) (B : Finset (Label V)) : Prop where
  rooted : ∀ x∈B,parent x∈F
  height : ∀ x∈B,HeightBound h x
  before : Before key B
  card : B.card ≤ size

end MetricKMedianRecovery.RationalLeaves

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves RationalHeight
variable {V : Type*} [DecidableEq V]

structure State.Resources (F : Finset V) (q h p : ℕ) (s : State V) : Prop where
  bank : BankBound F h (3*q) (q*(2*F.card+1)) s.B
  correction : s.correction.Bounded h
  oldPrice : Height s.lam p
  newPrice : Height s.lam' p

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoupledFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

def finish (B : Finset (Label V)) (lam : ℚ) (P T : List (List (Label V))) : Output V :=
  ⟨B,lam,P++T⟩

def sameState (B : Finset (Label V)) (lam : ℚ) (P T U : List (List (Label V))) : State V :=
  ⟨B,P,.identity,lam,lam,T,U⟩

end MetricKMedianRecovery.CanonicalCoupledMerge

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

def advanceState (s : State V) (G : List (Label V)) (T U : List (List (Label V))) : State V :=
  { s with P := s.P++[G],T := T,U := U }

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoupledLeaf
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

def leafState (B : Finset (Label V)) (P : List (List (Label V))) (lam : ℚ)
    (key : ℕ) (i : V) (H : List (Label V)) (l u : ℚ) (T U : List (List (Label V))) : State V :=
  ⟨insert (leaf key i u) B,P++[H++[leaf key i u]],.shorten key i l u,lam,lam,T,U⟩

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoupledResolve
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge

section
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge CanonicalLengthView
variable {V : Type*} [LinearOrder V] {d : ℕ}

def resolve (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v M : ℚ) (N precision q n k key : ℕ) (B : Finset (Label V)) (lam : ℚ)
    (P : List (List (Label V))) : CanonicalMergeCrossing.Result (Label V) → Outcome V
  | .success H T => .inl (finish B lam (P++[H]) T)
  | .common H T U => .inr (sameState B lam (P++[H]) T U)
  | .sensitive H G T U =>
    match view (rows distance) (F.image original) ((F.sort (·≤·)).map original) H G with
    | none => .inl (finish B lam P [])
    | some J =>
      let i := parent J.root
      let C := J.common H
      match CanonicalSensitiveEndpoint.run loc distance F (after ∅ P) v lam (20*N*M) q n k key precision H T U J with
      | .success s W => .inl (finish (insert (leaf key i s) B) lam (P++[C++[leaf key i s]]) W)
      | .bracket l u A Z => .inr (leafState B P lam key i C l u A Z)

attribute [local instance] RationalLeaves.metric

end

open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
attribute [local instance] RationalLeaves.metric

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyAge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves RationalHeight
variable {V : Type*} [DecidableEq V]

structure Output.Resources (F : Finset V) (q h p : ℕ) (o : Output V) : Prop where
  bank : BankBound F h (3*q) (q*(2*F.card+1)) o.B
  price : Height o.lam p

def Outcome.Resources (F : Finset V) (q h p : ℕ) : Outcome V → Prop
  | .inl o => o.Resources F (q+1) h p
  | .inr s => s.Resources F (q+1) h p

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Values
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryOpeningPayment
open WordList RationalLinearFeasibility

def pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : List Bool :=
  WordList.encode [Rectangular.encode distance,
    BinaryOpeningActivity.indices ((EffectiveOpenability.subtypeList W).map Subtype.val),
    BinaryRational.encode v,BinaryRational.encode z,BinaryRational.encode lam,
    BinaryRational.encode eta,i.val.bits,List.replicate d true,
    BinaryOpeningActivity.indices ((EffectiveOpenability.subtypeList F).map Subtype.val)]
end BinaryOpeningPayment
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_ObservableCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryZeroBranch
open WordOperations WordList BinaryBranchContext BinaryBranchProgram BinaryArithmetic
attribute [local instance] Classical.propDecidable
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (q : ℕ) (extra : List Bool) : List Bool :=
  BinaryBranchContext.pack δ D F S Δ s colors (fun _=>0 : Fin n→Fin 1) q 0 extra
end MetricKMedianRecovery.BitMachine.BinaryZeroBranch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SensitiveMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySensitive
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalLengthView
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_encode)
def pack {m : ℕ} (base : List Bool) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (H : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) (J : Plan (Label (Fin m))) : List Bool :=
  encode [base,List.replicate n true,List.replicate q true,key.bits,BinaryRational.encode b,k.bits,List.replicate N true,
    labels H,historyBits T,historyBits U,BinaryLength.planBits J]
lemma views_pack {m : ℕ} (base : List Bool) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (H : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) (J : Plan (Label (Fin m))) :
    common (pack base n q key b k N H T U J)=labels (J.common H) ∧
    small (pack base n q key b k N H T U J)=historyBits (J.small T U) ∧
    large (pack base n q key b k N H T U J)=historyBits (J.large T U) ∧
    jf 1 (pack base n q key b k N H T U J)=BinaryLabel.encode J.root := by
  cases J <;> simp [common,small,large,isFree,jf,pack,BinaryLength.planBits,
    field_encode,value,Plan.common,Plan.small,Plan.large,Plan.root,BinaryFiniteContext.labels_append]

end MetricKMedianRecovery.BitMachine.BinarySensitive

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CorrectionSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves
variable {V : Type*} [LinearOrder V] {d : ℕ}
def Outcome.Keys (q : ℕ) : Outcome V→Prop
  | .inl _=>True
  | .inr s=>s.correction.Keys (q+1)
end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_RefineMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRefine
open WordOperations WordList RationalLeaves CanonicalMergeRefinement
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_encode)
def ctxBits {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key spare : ℕ) : List Bool :=
  encode [setBits F,labels R,key.bits,spare.bits]
end MetricKMedianRecovery.BitMachine.BinaryRefine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ResolveMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryResolve
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge CanonicalLengthView
open BinaryOpeningPayment (field field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
def pack {m : ℕ} (base : List Bool) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (B : Finset (Label (Fin m))) (P : List (List (Label (Fin m)))) (R : CanonicalMergeCrossing.Result (Label (Fin m))) : List Bool :=
  encode [base,List.replicate n true,List.replicate q true,key.bits,BinaryRational.encode b,k.bits,List.replicate N true,
    setBits B,historyBits P,BinaryCross.resultBits R]
end MetricKMedianRecovery.BitMachine.BinaryResolve

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoupledInitial
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [LinearOrder V] {d : ℕ}

def initial (l u : ℚ) (T U : List (List (Label V))) : State V :=
  ⟨∅,[],.identity,l,u,T,U⟩

attribute [local instance] RationalLeaves.metric

end MetricKMedianRecovery.CanonicalCoupledMerge

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [LinearOrder V] {d : ℕ}

def initialHistory (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v lam : ℚ) (total : ℕ) : List (List (Label V)) :=
  FiniteLabelContinuation.continuation (fun j=>original (loc j)) (rows distance)
    (F.image original) v lam 0 total ∅

def initialCount (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v lam : ℚ) (total : ℕ) : ℕ :=
  ((after ∅ (initialHistory loc distance F v lam total))∩F.image original).card

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

def StartOutput.Correct (loc : Fin d → V) (F : Finset V) (v eta : ℝ) (lo M : ℚ)
    (total k : ℕ) : StartOutput V → Prop
  | .small o => o.B=∅ ∧ o.lam=lo ∧
      PrefixData (fun j=>original (loc j)) (F.image original) ∅ v lo eta total o.P ∧
      ((after ∅ o.P)∩F.image original).card≤k
  | .normal o => o.Correct loc F v eta lo (8*(d:ℝ)*(M:ℝ)) total k

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CanonicalParents
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves CanonicalLengthView
variable {V : Type*} [LinearOrder V] {d : ℕ}

def Outcome.Rooted (F : Finset V) : Outcome V→Prop
  | .inl o => CanonicalCoupledMerge.Rooted F o.B
  | .inr s => CanonicalCoupledMerge.Rooted F s.B

def StartOutput.Rooted (F : Finset V) : StartOutput V→Prop
  | .small o => CanonicalCoupledMerge.Rooted F o.B
  | .normal o => CanonicalCoupledMerge.Rooted F o.B
end MetricKMedianRecovery.CanonicalCoupledMerge

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves PhaseSequence PhaseHistoryTransfer PhaseMergeInvariant PhaseMergeCertificate HistoryPhaseBound
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

def Output.project (o : Output V) : Finset V := RationalLeaves.project (after ∅ o.P)

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialProject
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
variable {V : Type*} [LinearOrder V]
def StartOutput.project : StartOutput V→Finset V
  | .small o => o.project
  | .normal o => o.project
end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_SurplusPostprocess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field field_encode)
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
def pack (distance : Fin m→Fin d→ℚ) (F S : Finset (Fin m)) (k : ℕ) : List Bool :=
  encode [Rectangular.encode distance,List.replicate d true,BinaryFinSet.encode F,BinaryFinSet.encode S,k.bits]
end MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess

end OAI
end


