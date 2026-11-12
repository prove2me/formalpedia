-- Prove2me | Definitions.Def_Q238L054
-- name    : Q238L054
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T12:01:15.86001+00:00
-- url     : https://prove2.me/theorems/ccd9af4e-b8d1-4bd5-b50d-3fe465115b13
-- title:
--   Definitions bundle Q238L054 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 78 declarations of OpenAI's Lean: 78 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.A.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.call`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.call_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.counter`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.cut`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.cut_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.demand`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.demand_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.projectInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.projectInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.ready`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.ready_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.algorithm`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.budget`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.calls`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.calls_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.candidates`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.candidates_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.demand`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.demand_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.demands`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.demands_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.one`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.one_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.output`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.select`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.selectInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.selectInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.select_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.words`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.Dsp.budget`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.candidates_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.output`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.runInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.runInput_computes` and 38 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_GlobalCall`, `KMedianRecovery_Algorithms_GlobalOuter`, `KMedianRecovery_Algorithms_GlobalOuterProbability`, `KMedianRecovery_Algorithms_IntegralAll`, `KMedianRecovery_Algorithms_IntegralRecoveryAll`, `KMedianRecovery_Algorithms_IntegralRecoveryAmplified`, `KMedianRecovery_Algorithms_IntegralRecoveryGuesses`, `KMedianRecovery_Algorithms_IntegralRecoveryMachine`, `KMedianRecovery_Algorithms_IntegralRecoveryRepeat`, `KMedianRecovery_Algorithms_IntegralRecoverySuccess`, `KMedianRecovery_Branching_BranchPrefix`, `KMedianRecovery_Branching_ObservableCapacity`, `KMedianRecovery_Branching_RandomizedZeroBranch`, `KMedianRecovery_Machines_RecoveryOptionMachine`, `KMedianRecovery_Recovery_RecoveryEnumeration`, `KMedianRecovery_Sampling_SamplerDraw`, `KMedianRecovery_Sampling_SamplerResources`, `KMedianRecovery_Sampling_SamplerTraceMachine`, `KMedianRecovery_Sampling_SamplingPotential`, `KMedianRecovery_Strictness_MetricSurplus`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L051`, `Q238L052` and `Q238L053` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.algorithm_output_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.demand_bound_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.finite_program_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.select_bits_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalRounding.rounded_program_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.cost_le_start_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.cost_le_surplus_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.finite_program_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.lift_probability_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.output_feasible_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.run_output_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.uniform_program_long_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.algorithm_output_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.demand_bound_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.finite_program_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.select_bits_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalRounding.rounded_program_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.cost_le_start_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.cost_le_surplus_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.finite_program_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.lift_probability_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.output_feasible_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.run_output_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.uniform_program_long_s238r` and `OAI.MetricKMedianRecovery.global_application`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L051
import Definitions.Def_Q238L052
import Definitions.Def_Q238L053

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_ObservableCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch
open WordOperations WordList BinaryBranchContext BinaryObservableBranch
noncomputable def run_computes (d : ℕ) : PolyComputes (run d) :=
  (BinaryBranchRandomize.context_computes.pair BinaryBranchRandomize.tailBits_computes).comp
    (BinaryObservableBranch.run_computes d)
end MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RandomizedZeroBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch
open WordOperations WordList BinaryBranchContext
variable {n : ℕ}
noncomputable def run_computes : PolyComputes run :=
  (BinaryBranchRandomize.context_computes.pair BinaryBranchRandomize.tailBits_computes).comp BinaryZeroBranch.run_computes
end MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.Prefix
open WordOperations BinaryBranchContext
noncomputable def run_computes (d : ℕ) : PolyComputes (run d) :=
  BinaryBranchTape.Count.cut_computes.comp (BinaryRandomizedBranch.run_computes d)
end MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.Prefix
namespace MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix
open WordOperations
noncomputable def run_computes : PolyComputes run :=
  BinaryBranchTape.Count.cut_computes.comp BinaryRandomizedZeroBranch.run_computes
end MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RecoveryEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] context zeroContext BinaryRandomizedBranch.Prefix.run BinaryRandomizedZeroBranch.Prefix.run
noncomputable def atBranch_computes (d : ℕ) : PolyComputes (atBranch d) :=
  (context_computes.pair (src_computes 9)).comp (BinaryRandomizedBranch.Prefix.run_computes d)
noncomputable def atZero_computes : PolyComputes atZero :=
  ((promote_computes.comp zeroContext_computes).pair (src_computes 9)).comp BinaryRandomizedZeroBranch.Prefix.run_computes
attribute [local irreducible] mapWith
noncomputable def candidateWords_computes (d : ℕ) : PolyComputes (candidateWords d) :=
  (PolyComputes.comp (f := fun input=>pairBits (input,range input)) (g := mapWith atZero)
    (id_computes.pair range_computes) (mapWith_computes atZero_computes)).append
    (PolyComputes.comp (f := fun input=>pairBits (input,choices input)) (g := mapWith (atBranch d))
      (id_computes.pair choices_computes) (mapWith_computes (atBranch_computes d)))
attribute [local irreducible] metricContext candidateWords
noncomputable def run_computes (d : ℕ) : PolyComputes (run d) :=
  (metricContext_computes.pair ((field_computes 3).pair (candidateWords_computes d))).comp BinaryMetricBest.run_computes
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_RecoveryOptionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] run
noncomputable def atOption_computes (d : ℕ) : PolyComputes (atOption d) := by
  unfold atOption
  exact (discardPrefix_computes.comp isEmpty_computes).cond (src_computes 3)
    (replaceState_computes.comp (run_computes d))
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerDraw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Draw
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def index_computes : PolyComputes index :=
  (cons_computes (field_computes 2) (cons_computes weights_computes
    (cons_computes (const_computes _) (cons_computes (field_computes 3) (const_computes []))))).comp BinaryDyadic.run_computes
noncomputable def run_computes : PolyComputes run := (index_computes.pair actions_computes).comp Lookup.run_computes
end MetricKMedianRecovery.BitMachine.BinarySampler.Draw

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Loop
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] Update.run Draw.run
variable {n : ℕ}

noncomputable def step_computes : PolyComputes step := (input_computes.pair (drawInput_computes.comp Draw.run_computes)).comp Update.run_computes
end MetricKMedianRecovery.BitMachine.BinarySampler.Loop

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Loop
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def run_computes : PolyComputes run :=
  (cap.computes.pair (Fold.pack_computes (field_computes 3) fixedContext_computes (const_computes initial))).comp
    (CappedFold.run_computes step_computes)
end MetricKMedianRecovery.BitMachine.BinarySampler.Loop

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
noncomputable def atPrefix_computes : PolyComputes atPrefix :=
  (cons_computes (extractPrefix_computes.comp (field_computes 0))
    (cons_computes (extractPrefix_computes.comp (field_computes 1))
      (cons_computes (extractPrefix_computes.comp (field_computes 2))
        (cons_computes prefixBits_computes (const_computes []))))).comp Loop.run_computes
noncomputable def run_computes : PolyComputes run :=
  (input_computes.pair (((field_computes 2).append (const_computes [true])).comp BinaryEllipsoidInitial.indices_computes)).comp
    (mapWith_computes atPrefix_computes)
end MetricKMedianRecovery.BitMachine.BinarySampler.Trace

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] src mword extra completeRaw BinaryRational.natWords
attribute [local irreducible] mapWith recoveryContext sampleContext BinarySampler.Trace.run
noncomputable def candidateWords_computes (d : ℕ) : PolyComputes (candidateWords d) :=
  PolyComputes.comp
    (f := fun input=>pairBits (recoveryContext input,BinarySampler.Trace.run (sampleContext input)))
    (g := mapWith (BinaryRecovery.atOption d))
    (recoveryContext_computes.pair (PolyComputes.comp (f := sampleContext) (g := BinarySampler.Trace.run)
      sampleContext_computes BinarySampler.Trace.run_computes))
    (mapWith_computes (BinaryRecovery.atOption_computes d))
noncomputable def run_computes (d : ℕ) : PolyComputes (run d) :=
  (metricContext_computes.pair ((src_computes 4).pair (candidateWords_computes d))).comp BinaryMetricBest.run_computes
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoverySuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
open WordOperations WordList Sampling.Comparison BinaryArithmetic
attribute [local irreducible] mword precision sampleCount raw extra RawTake.run RawDrop.run
noncomputable def run_computes (d : ℕ) : PolyComputes (run d) := repack_computes.comp (BinaryIntegralRecovery.run_computes d)
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryRepeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat
open WordOperations WordList Sampling.Comparison
attribute [local irreducible] extra Fair.raw Fair.demandWord Fair.run BinaryMetricBest.run RawUnary.run BinarySeed.rows
  BinaryIntegralRecovery.result BinaryFinSet.encode BinarySampler.Parameters.pack BinaryMetricBest.best Fair.output List.ofFn BinarySeed.raw
noncomputable def atSeed_computes (d : ℕ) : PolyComputes (atSeed d) := atSeedInput_computes.comp (Fair.run_computes d)
attribute [local irreducible] mapWith
noncomputable def candidates_computes (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (candidates Q d) :=
  PolyComputes.comp (f := fun input=>pairBits (context input,rows Q input)) (g := mapWith (atSeed d))
    (context_computes.pair (rows_computes Q)) (mapWith_computes (atSeed_computes d))
noncomputable def run_computes (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (run Q d) :=
  (metricContext_computes.pair ((src_computes 4).pair (candidates_computes Q d))).comp BinaryMetricBest.run_computes
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryAmplified
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape
open WordOperations WordList Sampling.Comparison FiniteSampling
attribute [local irreducible] Repeat.run Fair.pack Fair.raw Repeat.rword Repeat.bword RawTake.run extra
attribute [local irreducible] demandBits
noncomputable def run_computes (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (run Q d) :=
  (cut_computes Q).comp (Repeat.run_computes Q d)
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryGuesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] Repeat.FiniteTape.run BinarySanitizedBest.run BinaryFinSet.encode BinarySampler.Parameters.unary Count.run src
noncomputable def atChoice_computes (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (atChoice Q d) :=
  atInput_computes.comp (Repeat.FiniteTape.run_computes Q d)
attribute [local irreducible] mapWith
noncomputable def candidateWords_computes (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (candidateWords Q d) :=
  PolyComputes.comp (f := fun input=>pairBits (input,choices input)) (g := mapWith (atChoice Q d))
    (id_computes.pair choices_computes) (mapWith_computes (atChoice_computes Q d))
attribute [local irreducible] sizeWord candidateWords
noncomputable def runInput_computes (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (runInput Q d) := list_computes
  [src 0,src 2,src 3,src 4,sizeWord,candidateWords Q d] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨src_computes _⟩ | exact ⟨sizeWord_computes⟩ | exact ⟨candidateWords_computes Q d⟩)
noncomputable def run_computes (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (run Q d) :=
  (runInput_computes Q d).comp BinarySanitizedBest.run_computes
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

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
noncomputable def cutRaw_computes (Q : Polynomial ℕ) : PolyComputes (cutRaw Q) :=
  (((demand_computes Q).comp UnaryResources.lengthBits_computes).pair (src_computes 7)).comp RawTake.run_computes
noncomputable def callInput_computes (Q : Polynomial ℕ) : PolyComputes (callInput Q) :=
  recoveryParams_computes.pair ((src_computes 6).pair (cutRaw_computes Q))
noncomputable def call_computes (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (call Q d) :=
  (callInput_computes Q).comp (BinaryIntegralRecovery.Guesses.run_computes Q d)
attribute [local irreducible] mapWith
noncomputable def calls_computes (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (calls Q d) :=
  PolyComputes.comp (f := fun input=>pairBits (input,ranks input)) (g := mapWith (call Q d))
    (id_computes.pair ranks_computes) (mapWith_computes (call_computes Q d))
noncomputable def start_computes : PolyComputes start := (id_computes.pair (field_computes 5)).comp anchor_computes
attribute [local irreducible] start calls
noncomputable def runInput_computes (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (runInput Q d) := list_computes
  [field 0,field 2,field 3,start,field 5,calls Q d] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨field_computes _⟩ | exact ⟨start_computes⟩ | exact ⟨calls_computes Q d⟩)
noncomputable def run_computes (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (run Q d) :=
  (runInput_computes Q d).comp BinarySanitizedBest.run_computes
end MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_MetricSurplus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricSurplus
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def run_computes (v : ℚ) (C : ℕ) : PolyComputes (run v C) :=
  runInput_computes.comp (BinaryCanonicalSurplus.run_computes v C)
end MetricKMedianRecovery.BitMachine.BinaryMetricSurplus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralAll
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
namespace Dsp
noncomputable abbrev budget := BinaryIntegralDispatch.budget
end Dsp
variable {n : ℕ}
noncomputable def surplus_computes (v : ℚ) (C : ℕ) : PolyComputes (surplus v C) :=
  surplusInput_computes.comp (BinaryMetricSurplus.run_computes v C)
attribute [local irreducible] mapWith
noncomputable def surplusCalls_computes (v : ℚ) (C : ℕ) : PolyComputes (surplusCalls v C) :=
  PolyComputes.comp (f := fun input=>pairBits (input,BinaryIntegralDispatch.ranks input))
    (g := mapWith (surplus v C))
    (id_computes.pair BinaryIntegralDispatch.ranks_computes) (mapWith_computes (surplus_computes v C))
noncomputable def candidates_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (candidates v C Q d) :=
  cons_computes (BinaryIntegralDispatch.run_computes Q d) (surplusCalls_computes v C)
noncomputable def runInput (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  encode [field 0 x,field 2 x,field 3 x,BinaryIntegralDispatch.start x,field 5 x,candidates v C Q d x]
noncomputable def runInput_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (runInput v C Q d) :=
  list_computes [field 0,field 2,field 3,BinaryIntegralDispatch.start,field 5,candidates v C Q d] (by
    intro f hf; refine Classical.choice ?_; simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨field_computes _⟩ | exact ⟨BinaryIntegralDispatch.start_computes⟩ | exact ⟨candidates_computes v C Q d⟩)
noncomputable def run (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : List Bool→ List Bool :=
  BinarySanitizedBest.run ∘ runInput v C Q d
noncomputable def run_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (run v C Q d) :=
  (runInput_computes v C Q d).comp BinarySanitizedBest.run_computes
noncomputable def words (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→ Fin n→ℚ)
    (D F : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) : List (List Bool) :=
  Dsp.run Q d (Dsp.pack δ D F Δ k g raw)::
    List.ofFn (fun L:Fin (F.card+1)=>surplus v C (pairBits (Dsp.pack δ D F Δ k g raw,L.val.bits)))
noncomputable def output (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→ Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) : Finset (Fin n) :=
  BinarySanitizedBest.output δ D F S k (words v C Q d δ D F Δ k g raw)
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

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
namespace A
noncomputable abbrev run := BinaryIntegralAll.run
end A
noncomputable def counter (Q : Polynomial ℕ) : PolynomialCounter (A.budget Q) := PolynomialCounter.choose _
noncomputable def demand (Q : Polynomial ℕ) : List Bool→List Bool := (counter Q).word ∘ base
noncomputable def demand_computes (Q : Polynomial ℕ) : PolyComputes (demand Q) := base_computes.comp (counter Q).computes
attribute [local irreducible] counter demand base RawTake.run UnaryResources.lengthBits
noncomputable def cut (Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  RawTake.run (pairBits (UnaryResources.lengthBits (demand Q x),field 2 x))
noncomputable def cut_computes (Q : Polynomial ℕ) : PolyComputes (cut Q) :=
  (((demand_computes Q).comp UnaryResources.lengthBits_computes).pair (field_computes 2)).comp RawTake.run_computes
noncomputable def ready (Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  encode [src 0 x,src 1 x,src 2 x,src 3 x,src 6 x,clamp x,field 0 x,cut Q x]
noncomputable def ready_computes (Q : Polynomial ℕ) : PolyComputes (ready Q) := by
  unfold ready
  simpa only [List.map_cons,List.map_nil] using list_computes
    [src 0,src 1,src 2,src 3,src 6,clamp,field 0,cut Q] (by
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
      · exact ⟨cut_computes Q⟩)
noncomputable def call (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : List Bool→List Bool := A.run v C Q d ∘ ready Q
noncomputable def call_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (call v C Q d) :=
  (ready_computes Q).comp (BinaryIntegralAll.run_computes v C Q d)
attribute [local irreducible] call BinaryIntegralAll.run BinaryIntegralDispatch.budget ready norm src clamp BinaryInputParser.Metric.count
noncomputable def projectInput (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  pairBits (BinaryInputParser.Metric.count (field 0 x),call v C Q d x)
noncomputable def projectInput_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (projectInput v C Q d) :=
  ((field_computes 0).comp BinaryInputParser.Metric.count_computes).pair (call_computes v C Q d)
noncomputable def run (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : List Bool→List Bool :=
  BinaryTaggedSets.unshift ∘ projectInput v C Q d
noncomputable def run_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (run v C Q d) :=
  (projectInput_computes v C Q d).comp BinaryTaggedSets.unshift_computes
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
noncomputable def one (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : List Bool→List Bool :=
  BinaryGlobalCall.run v C Q d ∘ callInput
noncomputable def one_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (one v C Q d) :=
  callInput_computes.comp (BinaryGlobalCall.run_computes v C Q d)
noncomputable def calls (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  mapWith (one v C Q d) (pairBits (x,scales (extractPrefix x)))
noncomputable def calls_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (calls v C Q d) := by
  unfold calls
  simpa only [Function.comp_def,id_eq] using
    (id_computes.pair (extractPrefix_computes.comp scales_computes)).comp (mapWith_computes (one_computes v C Q d))
noncomputable def demand (Q : Polynomial ℕ) : List Bool→List Bool := BinaryGlobalCall.demand Q ∘ callInput
noncomputable def demand_computes (Q : Polynomial ℕ) : PolyComputes (demand Q) := callInput_computes.comp (BinaryGlobalCall.demand_computes Q)
noncomputable def demands (Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  mapWith (demand Q) (pairBits (pairBits (x,[]),scales x))
noncomputable def demands_computes (Q : Polynomial ℕ) : PolyComputes (demands Q) := by
  unfold demands
  simpa only [Function.comp_def,id_eq] using
    ((id_computes.pair (const_computes [])).pair scales_computes).comp (mapWith_computes (demand_computes Q))
noncomputable def budget (Q : Polynomial ℕ) : Polynomial ℕ := (demands_computes Q).lengthPolynomial
noncomputable def candidates (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  cons (zero (extractPrefix x)) (calls v C Q d x)
noncomputable def candidates_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (candidates v C Q d) := by
  unfold candidates
  simpa only [Function.comp_def] using
    cons_computes (extractPrefix_computes.comp zero_computes) (calls_computes v C Q d)
attribute [local irreducible] BinaryInputParser.Metric.matrix BinaryNormalizeInput.P.clients
  BinaryNormalizeInput.P.facilities BinaryInputParser.Metric.budget fallback candidates
noncomputable def selectInput (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  encode [P.matrix (extractPrefix x),P.clients (extractPrefix x),P.facilities (extractPrefix x),
    fallback (extractPrefix x),P.budget (extractPrefix x),candidates v C Q d x]
noncomputable def selectInput_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (selectInput v C Q d) :=
  cons_computes (extractPrefix_computes.comp BinaryInputParser.Metric.matrix_computes)
    (cons_computes (extractPrefix_computes.comp BinaryNormalizeInput.P.clients_computes)
      (cons_computes (extractPrefix_computes.comp BinaryNormalizeInput.P.facilities_computes)
        (cons_computes (extractPrefix_computes.comp fallback_computes)
          (cons_computes (extractPrefix_computes.comp BinaryInputParser.Metric.budget_computes)
            (cons_computes (candidates_computes v C Q d) (const_computes []))))))
noncomputable def select (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : List Bool→List Bool :=
  BinarySanitizedBest.run ∘ selectInput v C Q d
noncomputable def select_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (select v C Q d) :=
  (selectInput_computes v C Q d).comp BinarySanitizedBest.run_computes
noncomputable def run (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  BinaryMaskOutput.run (pairBits (maskCount x,select v C Q d x))
noncomputable def run_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (run v C Q d) :=
  (maskCount_computes.pair (select_computes v C Q d)).comp BinaryMaskOutput.run_computes
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalOuter
open WordOperations WordList LocalSearch Completion
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryGlobalCall.run BinaryGlobalCall.demand budget select BinarySanitizedBest.output
noncomputable def words (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (I : RationalMetricInput) (raw : List Bool) : List (List Bool) :=
  zero I.bits::(BinaryInputParser.Metric.flat I).map (fun M=>BinaryGlobalCall.run v C Q d (BinaryGlobalCall.pack I M raw))
noncomputable def output (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (I : RationalMetricInput) (raw : List Bool) : Finset (Fin I.pointCount) :=
  BinarySanitizedBest.output I.distance I.clients I.facilities (start I) I.budget (words v C Q d I raw)
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalOuterProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalOuter
open IntegralAssembly FiniteSampling Sampling.Comparison
attribute [local irreducible] output run budget
noncomputable def algorithm (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : BinaryRandomizedAlgorithm where
  randomBits := budget Q
  run := fun p=>run v C Q d (pairBits p)
  computation := (run_computes v C Q d).reencode pairBits id (fun _=>rfl)
  finiteWorkAlphabet := by
    intro k
    change Finite Bool
    infer_instance
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end


