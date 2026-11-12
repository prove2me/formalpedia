-- Prove2me | Definitions.Def_Q238L021
-- name    : Q238L021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:24:17.162168+00:00
-- url     : https://prove2.me/theorems/9bf6adcd-2cae-445f-83c9-2b12834e31bd
-- title:
--   Definitions bundle Q238L021 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 12 definitions and 1 theorem. The definitions and types are `OAI.MetricKMedianRecovery.Sampling.Comparison.endpointCharge`, `OAI.MetricKMedianRecovery.Sampling.Comparison.guidedUpdate`, `OAI.MetricKMedianRecovery.Sampling.Comparison.history`, `OAI.MetricKMedianRecovery.Sampling.Comparison.integralActions`, `OAI.MetricKMedianRecovery.Sampling.Comparison.samplingBound`, `OAI.MetricKMedianRecovery.Sampling.Comparison.samplingRate`, `OAI.MetricKMedianRecovery.Sampling.Comparison.stoppedActual`, `OAI.MetricKMedianRecovery.Sampling.Comparison.thirdSteps`, `OAI.MetricKMedianRecovery.Sampling.Precision.Good`, `OAI.MetricKMedianRecovery.Sampling.branchScore`, `OAI.MetricKMedianRecovery.ValidExecution.RegularFreezesAt`, `OAI.MetricKMedianRecovery.ValidExecution.removalReplay`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedianRecovery_Algorithms_IntegralPrecision`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/IntegralPrecision.lean), [`KMedianRecovery_Branching_SuccessfulFavorableProbability`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/SuccessfulFavorableProbability.lean), [`KMedianRecovery_Encoding_EntryIndex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/EntryIndex.lean), [`KMedianRecovery_Recovery_BlindUpdate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/BlindUpdate.lean), [`KMedianRecovery_Recovery_Destinations`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Destinations.lean), [`KMedianRecovery_Recovery_Guide`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Guide.lean), [`KMedianRecovery_Recovery_Removal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Removal.lean), [`KMedianRecovery_Recovery_RemovalReplay`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/RemovalReplay.lean), [`KMedianRecovery_Sampling_SamplingRate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplingRate.lean), [`KMedianRecovery_Strictness_RegularDualWitness`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Strictness/RegularDualWitness.lean).
--
--   **Imports.** It imports the bundles `Q238L006`, `Q238L010`, `Q238L011` and `Q238L012` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.favorable_literal_plan_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.objective_eq_source_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.planned_successful_completion_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output_success_s238r`, `OAI.MetricKMedianRecovery.Sampling.Comparison.guideLoss_domination_s238r`, `OAI.MetricKMedianRecovery.Sampling.Comparison.history_menu_budget_s238r` and `OAI.MetricKMedianRecovery.Sampling.Comparison.integral_records_success_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.favorable_literal_plan_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.objective_eq_source_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.planned_successful_completion_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output_success_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.polynomial_program_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.successful_probability_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.successful_completion_s238r`, `OAI.MetricKMedianRecovery.HistoryCompatibleCertificate.compatible_certificate_s238r`, `OAI.MetricKMedianRecovery.Sampling.Comparison.guideLoss_domination_s238r`, `OAI.MetricKMedianRecovery.Sampling.Comparison.history_menu_budget_s238r`, `OAI.MetricKMedianRecovery.Sampling.Comparison.integralPrecision_spec_s238r`, `OAI.MetricKMedianRecovery.Sampling.Comparison.integral_records_success_s238r`, `OAI.MetricKMedianRecovery.Sampling.Comparison.surrogate_success_s238r` and `OAI.MetricKMedianRecovery.valid_execution_bounded_price_strictness_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_Q238L006
import Definitions.Def_Q238L010
import Definitions.Def_Q238L011
import Definitions.Def_Q238L012

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
-- module Solutions.Q238_KM.KMedianRecovery_Branching_SuccessfulFavorableProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
open Completion Categorical FiniteSampling Comparison
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable def branchScore (D S : Finset V) (Δ : ℝ) (s : State V) (u v : V) : ℝ :=
  assignmentWeight D (completionAssignment S Δ s) u * dist u v

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

noncomputable def stoppedActual (C : Comparison D S O) (hD : D.Nonempty) (Δ : ℝ) :=
  Guided.stoppedKernel (mainActual D S Δ C.bad.card) (C.stop hD Δ) (.inl ())

noncomputable def guidedUpdate (C : Comparison D S O) (hD : D.Nonempty) (F : Finset V) (Δ : ℝ) :=
  Guided.stoppedUpdate
    (update D F S hD Δ (comparisonCost D C.assign) mainKappa C.bad.card
      (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa C.bad.card))
    (C.stop hD Δ)

noncomputable def history (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (Δ : ℝ) (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (i : Fin (n+1)) : State V :=
  (Guided.states (C.guidedUpdate hD F Δ) n (some State.initial) seed i).getD State.initial

noncomputable def thirdSteps {m n : ℕ} (seed : Fin n → MainAction D m) : Finset (Fin n) :=
  Finset.univ.filter (fun i => IsThird (seed i))

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_EntryIndex
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

noncomputable def samplingBound (m : ℕ) : ℝ :=
  NearClients.progressConstant mainKappa ^ (2*m) * (menuConstant mainKappa mainKappa_pos)^m *
    (2 : ℝ)^(-((10/(9*mainKappa)+1)*m))

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open MetricKMedianRecovery RadiusMenus

noncomputable def samplingRate : ℝ :=
  NearClients.progressConstant mainKappa ^ 2 * menuConstant mainKappa mainKappa_pos *
    (2:ℝ)^(-(10/(9*mainKappa)+1))

end MetricKMedianRecovery.Sampling.Comparison

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Removal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

namespace ValidExecution

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {steps : ℕ} {v lam eta : ℝ} (E : ValidExecution D X steps v lam eta)

lemma no_overbid (hv : 0 < v) (hv1 : v < 1 / 6) (hlam : 0 < lam)
    (n : ℕ) (hn : n ≤ steps) :
    ∀ i ∈ E.regular,
      bidRow E.location (1 - 3 * v) (E.state n).phase (E.state n).opened i ≤ lam := by
  induction n with
  | zero =>
    intro i hi
    rw [E.initial]
    have heq : bidRow E.location (1 - 3 * v) (initialState D X).phase
        (initialState D X).opened i = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp only [initialState, clippedAt, Finset.not_nonempty_empty, ↓reduceIte]
      exact max_eq_right (by linarith only [E.far_initially j i hi])
    rw [heq]
    exact hlam.le
  | succ n ih =>
    exact (E.transition n (by omega)).preserves_no_overbid hv hv1
      (E.phase_pos n (by omega)) hlam (ih (by omega))

end ValidExecution

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RemovalReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

namespace ValidExecution

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {steps : ℕ} {v lam eta : ℝ} (E : ValidExecution D X steps v lam eta)

noncomputable def removalReplay (hv : 0 < v) (hv1 : v < 1 / 6) (hlam : 0 < lam) :
    RemovalReplay D X steps (1 - 3 * v) (1 + v ^ 2) lam where
  location := E.location
  regular := E.regular
  before := fun n => (E.state n).opened
  after := fun n => (E.state (n.val + 1)).opened
  phase := fun n => (E.state n).phase
  removal := E.removal
  budget := (E.state steps).budget
  phase_nonneg := fun n => (E.phase_pos n n.isLt.le).le
  before_mono := fun _ b hab => E.opened_mono hab b.isLt.le
  after_in_later := fun _ b hab => E.opened_mono (Nat.succ_le_of_lt hab) b.isLt.le
  active_threshold := fun j f hf => (E.removal_active j f hf).le
  post_removal := fun j => (E.transition _ (E.removal j).isLt).removal_connection_cap hv1
    (E.phase_pos _ (E.removal j).isLt.le).le j (E.removal_inactive j)
  final_cap := E.final_cap
  no_overbid := by
    intro n i hi
    convert E.no_overbid hv hv1 hlam n n.isLt.le i hi using 1
    all_goals try with_reducible_and_instances rfl
    unfold bidRow
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    by_cases hj : E.removal j < n
    · rw [ite_eq_left hj]
      exact (clippedAt_of_inactive E.location (1 - 3 * v) (E.state n).phase
        (E.state n).opened j (by linarith only [hv1])
        (fun h => not_le_of_gt hj ((E.active_iff_before_removal n n.isLt.le j).mp h))).symm
    · rw [ite_eq_right hj]
      exact (clippedAt_of_active E.location (1 - 3 * v) (E.state n).phase
        (E.state n).opened j (by linarith only [hv1])
        ((E.active_iff_before_removal n n.isLt.le j).mpr (le_of_not_gt hj))).symm

end ValidExecution

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_RegularDualWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

namespace ValidExecution

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {steps : ℕ} {v lam eta : ℝ} (E : ValidExecution D X steps v lam eta)

def RegularFreezesAt (i : X) (n : ℕ) : Prop :=
  ∃ W : RegularDualWitness E.location E.regular v lam (E.state n) (E.state (n + 1)),
    dist i W.facility ≤ (1 + 3 * v) * (E.state n).phase / 2

end ValidExecution

end MetricKMedianRecovery

end OAI
end


