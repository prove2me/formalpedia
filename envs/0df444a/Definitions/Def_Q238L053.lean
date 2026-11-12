-- Prove2me | Definitions.Def_Q238L053
-- name    : Q238L053
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:55:23.645316+00:00
-- url     : https://prove2.me/theorems/3500e15f-369a-4b34-87f3-8bdda73aa687
-- title:
--   Definitions bundle Q238L053 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 30 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.base_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.clamp_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.fcount_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.norm_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.src_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.fallback_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.zeroInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.zero_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.matrix_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows.row_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.output`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.words`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.cap_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.matrix_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.mesh_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.prep_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.rounded_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.prefixBits_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.remove_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.remove_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySanitizedBest.atRaw_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySanitizedBest.candidates_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySanitizedBest.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.check_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.completion_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.run_computes`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_CandidateSanitize`, `KMedianRecovery_Algorithms_GlobalCall`, `KMedianRecovery_Algorithms_GlobalOuter`, `KMedianRecovery_Algorithms_IntegralDispatchLaws`, `KMedianRecovery_Algorithms_IntegralRecoveryAll`, `KMedianRecovery_Branching_BranchObjective`, `KMedianRecovery_Branching_ObservableCapacity`, `KMedianRecovery_Encoding_MatrixRows`, `KMedianRecovery_Geometry_MetricParser`, `KMedianRecovery_Recovery_NormalizeInput`, `KMedianRecovery_Sampling_SamplerTraceMachine`, `KMedianRecovery_Sampling_SamplerUpdate`, `KMedianRecovery_Sampling_SamplingStateMachine`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L048`, `Q238L049` and `Q238L050` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q238L054`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.cost_le_call_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.designated_recovery_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.run_output_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.cost_le_call_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.designated_recovery_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.run_output_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L048
import Definitions.Def_Q238L049
import Definitions.Def_Q238L050

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_MatrixRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows
open WordOperations WordList BinaryArithmetic
attribute [local irreducible] offset Drop.run Take.run
noncomputable def row_computes : PolyComputes row :=
  (((extractPrefix_computes.comp extractPrefix_computes).comp UnaryResources.lengthBits_computes).pair
    ((offset_computes.pair (extractPrefix_computes.comp discardPrefix_computes)).comp Drop.run_computes)).comp Take.run_computes
attribute [local irreducible] mapWith
noncomputable def run_computes : PolyComputes run := by
  unfold run
  exact (id_computes.pair (extractPrefix_computes.comp BinaryEllipsoidInitial.indices_computes)).comp (mapWith_computes row_computes)
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricParser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric
open WordOperations WordList
attribute [local irreducible] nat RawTake.run RawDrop.run Stream.run Rows.run RawUnary.run
attribute [local irreducible] header count tailHeader budget masks clients afterClients facilities rawMatrix
noncomputable def matrix_computes : PolyComputes matrix := by
  unfold matrix
  exact ((clients_computes.comp RawUnary.run_computes).pair (rawMatrix_computes.comp Stream.run_computes)).comp Rows.run_computes
attribute [local irreducible] matrix
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingStateMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingState
open WordOperations WordList BinaryArithmetic RationalSampling
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def remove_computes : PolyComputes remove :=
  (((extractPrefix_computes.comp extractPrefix_computes).pair
    (cons_computes discardPrefix_computes (const_computes []))).comp BinaryNatSet.union_computes).pair
    (extractPrefix_computes.comp discardPrefix_computes)
end MetricKMedianRecovery.BitMachine.BinarySamplingState

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_CandidateSanitize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySanitizedBest
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def atRaw_computes : PolyComputes atRaw := atRawInput_computes.comp BinaryCandidateSanitize.run_computes
noncomputable def candidates_computes : PolyComputes candidates := by
  have candidatesComputes := (sanitizeContext_computes.pair (field_computes 5)).comp (mapWith_computes atRaw_computes)
  unfold candidates
  simpa only [Function.comp_def] using candidatesComputes
noncomputable def run_computes : PolyComputes run :=
  (metricContext_computes.pair ((field_computes 3).pair candidates_computes)).comp BinaryMetricBest.run_computes
end MetricKMedianRecovery.BitMachine.BinarySanitizedBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchObjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryObservableBranch
open WordOperations WordList BinaryBranchContext BinaryBranchProgram
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ}
noncomputable def run_computes (d : ℕ) : PolyComputes (run d) := by
  unfold run
  simpa only [Function.comp_def,decide_eq_true_eq] using
    (extractPrefix_computes.comp BinaryBranchCheck.run_computes).cond
      (((extractPrefix_computes.comp (best_computes d)).comp isEmpty_computes).cond
        (extractPrefix_computes.comp (field_computes 3)) (BinaryBranchProgram.run_computes d))
      (extractPrefix_computes.comp (field_computes 3))
end MetricKMedianRecovery.BitMachine.BinaryObservableBranch

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
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def check_computes : PolyComputes (fun x=>[check x]) := by
  simpa only [check,Bool.decide_and,Function.comp_def] using
    (BinaryBranchCheck.outside_computes.comp isEmpty_computes).and
      ((BinaryBranchCheck.badBalls_computes.comp isEmpty_computes).and
        ((BinaryBranchCheck.badRadii_computes.comp isEmpty_computes).and
          ((NatOps.le (field_computes 9) ((classOf_computes 1).comp lengthBits_computes)).and
            (NatOps.le BinaryBranchCheck.lhs_computes rhs_computes))))
noncomputable def completion_computes : PolyComputes completion :=
  cons_computes (field_computes 2) (cons_computes (field_computes 3)
    (cons_computes ((field_computes 5).comp extractPrefix_computes) (cons_computes parts_computes
      (cons_computes origins_computes (cons_computes locations_computes (cons_computes (classOf_computes 1)
        (cons_computes (const_computes []) (cons_computes (const_computes [])
          (cons_computes (const_computes []) (cons_computes rows_computes (const_computes [])))))))))))
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [Function.comp_def] using
    (extractPrefix_computes.comp check_computes).cond
      (((extractPrefix_computes.comp completion_computes).pair discardPrefix_computes).comp BinaryCompletionFair.run_computes)
      (extractPrefix_computes.comp (field_computes 3))
end MetricKMedianRecovery.BitMachine.BinaryZeroBranch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Update
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open Weights (actionField actionField_computes)
attribute [local irreducible] radius
variable {n : ℕ}
noncomputable def remove_computes : PolyComputes remove :=
  ((input_computes.comp (c_computes 8)).pair (((input_computes.comp discardPrefix_computes).pair chosen_computes).comp
    BinarySamplingState.remove_computes)).comp BinarySamplingState.retain_computes
noncomputable def run_computes : PolyComputes run := by
  have hh := active_computes.cond ((Weights.kind_computes 0).cond (const_computes [])
    ((Weights.kind_computes 1).cond (old_computes.cond remove_computes (const_computes []))
      ((radius_computes.comp isEmpty_computes).cond (const_computes [])
        ((ball_computes.comp isEmpty_computes).cond (const_computes []) add_computes)))) (const_computes [])
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [run,decide_eq_true_eq]

end MetricKMedianRecovery.BitMachine.BinarySampler.Update

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerTraceMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Trace
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinarySeed.rows Take.run Loop.run BinaryEllipsoidInitial.indices WordList.mapWith
noncomputable def prefixBits_computes : PolyComputes prefixBits :=
  (discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 3))).comp Take.run_computes
end MetricKMedianRecovery.BitMachine.BinarySampler.Trace

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
attribute [local irreducible] counter demand bare RawTake.run UnaryResources.lengthBits BinaryIntegralRecovery.Guesses.budget BinaryIntegralRecovery.Guesses.run
attribute [local irreducible] mapWith
attribute [local irreducible] start calls
noncomputable def words (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
    (D F : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) : List (List Bool) :=
  List.ofFn (fun r:Fin (F.card+1)=>call Q d (pairBits (pack δ D F Δ k g raw,r.val.bits)))
end MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralDispatchLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch
open WordOperations WordList Completion Sampling.Comparison FiniteSampling
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] anchor BinaryMetricAnchor.run BinaryIntegralRecovery.Guesses.run recoveryParams demand 
variable {n : ℕ}
noncomputable def output (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) : Finset (Fin n) :=
  BinarySanitizedBest.output δ D F S k (words Q d δ D F Δ k g raw)
end MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NormalizeInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNormalizeInput
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] P.points P.clients P.facilities
  BinaryInputParser.Metric.matrix BinaryInputParser.Metric.count BinaryInputParser.Metric.budget
  BinaryNormalization.run BinaryNormalization.cap BinaryNormalization.mesh
noncomputable def matrix_computes : PolyComputes matrix := raw_computes.comp BinaryInputParser.Metric.matrix_computes
noncomputable def prep_computes : PolyComputes prep := list_computes [matrix,points,clientCount,discardPrefix] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl
  · exact ⟨matrix_computes⟩
  · exact ⟨points_computes⟩
  · exact ⟨clientCount_computes⟩
  · exact ⟨discardPrefix_computes⟩)
noncomputable def rounded_computes : PolyComputes rounded := prep_computes.comp BinaryNormalization.run_computes
noncomputable def mesh_computes : PolyComputes mesh := prep_computes.comp BinaryNormalization.mesh_computes
noncomputable def cap_computes : PolyComputes cap := prep_computes.comp BinaryNormalization.cap_computes
noncomputable def run_computes : PolyComputes run := list_computes [rounded,twice,clients,facilities,budget,mesh,cap] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨rounded_computes⟩
  · exact ⟨twice_computes⟩
  · exact ⟨clients_computes⟩
  · exact ⟨facilities_computes⟩
  · exact ⟨budget_computes⟩
  · exact ⟨mesh_computes⟩
  · exact ⟨cap_computes⟩)
end MetricKMedianRecovery.BitMachine.BinaryNormalizeInput

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalCall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalCall
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def norm_computes : PolyComputes norm := normInput_computes.comp BinaryNormalizeInput.run_computes
noncomputable def src_computes (j : ℕ) : PolyComputes (src j) := norm_computes.comp (field_computes j)
noncomputable def fcount_computes : PolyComputes fcount := ((src_computes 3).comp Count.run_computes).comp UnaryResources.lengthBits_computes
noncomputable def clamp_computes : PolyComputes clamp := NatOps.min (src_computes 4) fcount_computes
noncomputable def base_computes : PolyComputes base := by
  unfold base
  simpa only [List.map_cons,List.map_nil] using list_computes
    [src 0,src 1,src 2,src 3,src 6,clamp,field 0,fun _=>[]] (by
      intro candidate member;refine Classical.choice ?_
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨src_computes 0⟩
      · exact ⟨src_computes 1⟩
      · exact ⟨src_computes 2⟩
      · exact ⟨src_computes 3⟩
      · exact ⟨src_computes 6⟩
      · exact ⟨clamp_computes⟩
      · exact ⟨field_computes 0⟩
      · exact ⟨const_computes []⟩)
attribute [local irreducible] base RawTake.run UnaryResources.lengthBits
attribute [local irreducible] norm src clamp BinaryInputParser.Metric.count
end MetricKMedianRecovery.BitMachine.BinaryGlobalCall

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalOuter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalOuter
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def fallback_computes : PolyComputes fallback := fallbackInput_computes.comp BinaryCompletionPad.run_computes
noncomputable def zeroInput_computes : PolyComputes zeroInput := cons_computes BinaryInputParser.Metric.matrix_computes
  (cons_computes BinaryNormalizeInput.P.clients_computes (cons_computes BinaryNormalizeInput.P.facilities_computes (const_computes [])))
noncomputable def zero_computes : PolyComputes zero := zeroInput_computes.comp BinaryGlobalZero.run_computes
attribute [local irreducible] BinaryInputParser.Metric.matrix BinaryNormalizeInput.P.clients
  BinaryNormalizeInput.P.facilities BinaryInputParser.Metric.budget fallback
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end


