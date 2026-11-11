-- Prove2me | Definitions.Def_Q238K023
-- name    : Q238K023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:16:11.66008+00:00
-- url     : https://prove2.me/theorems/fbbf1215-e9a2-47be-abd2-7cec48a2bae7
-- title:
--   Definitions bundle Q238K023 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 3 definitions and 1 theorem. The definitions and types are `OAI.MetricKMedianRecovery.Sampling.Comparison.samplingBound`, `OAI.MetricKMedianRecovery.Sampling.Comparison.samplingRate`, `OAI.MetricKMedianRecovery.ValidExecution.removalReplay`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedianRecovery_Encoding_EntryIndex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/EntryIndex.lean), [`KMedianRecovery_Recovery_Removal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Removal.lean), [`KMedianRecovery_Recovery_RemovalReplay`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/RemovalReplay.lean), [`KMedianRecovery_Sampling_SamplingRate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplingRate.lean).
--
--   **Imports.** It imports the bundles `Q238K006`, `Q238K015` and `Q238K016` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI_MetricKMedianRecovery_BitMachine_BinaryBlueBlocks_run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryBlueRecords_run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryBranchRows_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output_success_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryLabelSelect_run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_Rectangular_mulVec_encode_s238` and `OAI.MetricKMedianRecovery.Sampling.Comparison.integral_records_success_s238`; the proofs of `OAI_MetricKMedianRecovery_BitMachine_BinaryBlueBlocks_run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryExactSolve_run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryFace_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output_success_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.polynomial_program_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryLabelSelect_run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_Rectangular_mulVec_encode_s238`, `OAI_MetricKMedianRecovery_BitMachine_WordList_CappedFold_run_typed_s238`, `OAI.MetricKMedianRecovery.HistoryCompatibleCertificate.compatible_certificate_s238`, `OAI.MetricKMedianRecovery.Sampling.Comparison.integral_records_success_s238` and `OAI.MetricKMedianRecovery.valid_execution_bounded_price_strictness_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_Q238K006
import Definitions.Def_Q238K015
import Definitions.Def_Q238K016

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


