-- Prove2me | Definitions.Def_Q238K040
-- name    : Q238K040
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:37:30.702339+00:00
-- url     : https://prove2.me/theorems/56094188-5afa-4c35-9fc7-6f68ebe5e67e
-- title:
--   Definitions bundle Q238K040 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 59 declarations of OpenAI's Lean: 59 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueChoice.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueChoice.select_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueChoice.step_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.cap_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.weightedCap_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.base`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.clamp`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.fcount`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.norm`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.src`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.P.matrix`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.fallback`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.zero`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.zeroInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.matrix`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows.row`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.R.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.start`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.atChoice`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.candidateWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.output`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.runInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.words`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.atSeed`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.candidates`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.candidateWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.cap`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.matrix`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.mesh`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.prep`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.rounded`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseAdvance.budgetItem_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseAdvance.budget_computes` and 19 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_GlobalCall`, `KMedianRecovery_Algorithms_GlobalOuter`, `KMedianRecovery_Algorithms_IntegralRecoveryAll`, `KMedianRecovery_Algorithms_IntegralRecoveryAmplified`, `KMedianRecovery_Algorithms_IntegralRecoveryGuesses`, `KMedianRecovery_Algorithms_IntegralRecoveryMachine`, `KMedianRecovery_Algorithms_IntegralRecoveryRepeat`, `KMedianRecovery_Algorithms_IntegralRecoverySelection`, `KMedianRecovery_Algorithms_IntegralRecoverySuccess`, `KMedianRecovery_Branching_BlueChoice`, `KMedianRecovery_Branching_PopulationMachine`, `KMedianRecovery_Encoding_MatrixRows`, `KMedianRecovery_Encoding_RationalCap`, `KMedianRecovery_Geometry_MetricParser`, `KMedianRecovery_Machines_RecoveryOptionMachine`, `KMedianRecovery_Recovery_Min`, `KMedianRecovery_Recovery_NormalizeInput`, `KMedianRecovery_Recovery_RecoveryEnumeration`, `KMedianRecovery_Sampling_SamplerDraw`, `KMedianRecovery_Sampling_SamplerResources`, `KMedianRecovery_Sampling_SamplerTraceMachine`, `KMedianRecovery_Sampling_SamplingPotential`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K036`, `Q238K037` and `Q238K038` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K041`, `Q238K042` and `Q238K043`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.fallback_bits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.zero_bits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.run_source_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.cost_le_designated_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.run_output_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.polynomial_program_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.run_source_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.prep_bits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atOption_none_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.run_source_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.atPrefix_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.run_pack_s238`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.fallback_bits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.zero_bits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.run_source_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.cost_le_designated_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.run_output_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.polynomial_program_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.run_source_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.prep_bits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atOption_none_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.run_source_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.atPrefix_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.run_pack_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K036
import Definitions.Def_Q238K037
import Definitions.Def_Q238K038

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Min
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic WordList
namespace RatOps
noncomputable def min {f g : List Bool → ℚ}
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>BinaryRational.encode (min (f x) (g x))) := by
  have hh := (le hf hg).cond hf hg
  simpa only [decide_eq_true_eq,min_def,apply_ite] using hh
end RatOps
namespace BinaryPhaseAdvance
open EffectiveOpenability RationalPhase BinaryPhaseUpdate BinaryOpeningPayment

noncomputable def isActive_computes : PolyComputes (fun x=>[isActive x]) := query_computes.comp BinaryOpeningPayment.active_computes
noncomputable def nearest_computes : PolyComputes (fun x=>BinaryRational.encode (nearest x)) := by
  have nearestComputes := RatOps.ofWords
    ((query_computes.comp BinaryOpeningPayment.activityInput_computes).comp BinaryOpeningNearest.run_computes)
  unfold nearest
  simpa only [Function.comp_def] using nearestComputes
noncomputable def clippedItem_computes : PolyComputes (fun x=>BinaryRational.encode (clippedItem x)) := by
  have phaseComputes : PolyComputes
      (fun input=>BinaryRational.encode (phase (extractPrefix input))) := by
    simpa only [Function.comp_def] using (extractPrefix_computes.comp phase_computes)
  have paramVComputes : PolyComputes
      (fun input=>BinaryRational.encode (paramV (extractPrefix input))) := by
    simpa only [Function.comp_def] using (extractPrefix_computes.comp paramV_computes)
  have boundComputes := RatOps.mul
    (RatOps.sub (RatOps.const 1) (RatOps.mul (RatOps.const 3) paramVComputes)) nearest_computes
  have emptyComputes : PolyComputes (fun input=>[decide (sf 1 (extractPrefix input)=[])]) := by
    simpa only [Function.comp_def] using
      ((extractPrefix_computes.comp (sf_computes 1)).comp isEmpty_computes)
  have clippedComputes := emptyComputes.cond phaseComputes (RatOps.min phaseComputes boundComputes)
  unfold clippedItem
  simpa only [decide_eq_true_eq,apply_ite] using clippedComputes
noncomputable def budgetItem_computes : PolyComputes budgetItem := isActive_computes.cond clippedItem_computes
  ((discardPrefix_computes.pair (extractPrefix_computes.comp discardPrefix_computes)).comp Lookup.run_computes)
noncomputable def budget_computes : PolyComputes budget := by
  have budgetComputes :=
    (id_computes.pair (extractPrefix_computes.comp BinaryOpeningEnumeration.clients_computes)).comp
      (mapWith_computes budgetItem_computes)
  unfold budget
  simpa only [Function.comp_def,id_eq] using budgetComputes
noncomputable def run_computes : PolyComputes run := context_computes.pair budget_computes
end BinaryPhaseAdvance
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_MatrixRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows
open WordOperations WordList BinaryArithmetic
noncomputable def row (x : List Bool) : List Bool := Take.run (pairBits
  (UnaryResources.lengthBits (extractPrefix (extractPrefix x)),Drop.run (pairBits (offset x,discardPrefix (extractPrefix x)))))
attribute [local irreducible] offset Drop.run Take.run
noncomputable def run (x : List Bool) : List Bool :=
  mapWith row (pairBits (x,BinaryEllipsoidInitial.indices (extractPrefix x)))
attribute [local irreducible] mapWith
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
noncomputable def matrix (x : List Bool) : List Bool := Rows.run (pairBits (RawUnary.run (clients x),Stream.run (rawMatrix x)))
attribute [local irreducible] matrix
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_PopulationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPopulation
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] WordList.mapWith
noncomputable def near_computes : PolyComputes (fun x=>[near x]) :=
  RatOps.le (RatOps.ofWords discardPrefix_computes) (RatOps.ofWords extractPrefix_computes)
noncomputable def count_computes : PolyComputes count :=
  ((filterWith_computes near_computes).comp Count.run_computes).comp UnaryResources.lengthBits_computes
noncomputable def candidate_computes : PolyComputes (fun x=>BinaryRational.encode (candidate x)) :=
  RatOps.max (RatOps.ofWords discardPrefix_computes)
    (RatOps.div (RatOps.ofWords (extractPrefix_computes.comp (field_computes 0)))
      (RatOps.mul (RatOps.nat (extractPrefix_computes.comp (field_computes 1)))
        (RatOps.nat ((discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 2))).comp count_computes))))
noncomputable def candidates_computes : PolyComputes candidates :=
  (id_computes.pair (field_computes 2)).comp (mapWith_computes candidate_computes)
noncomputable def run_computes : PolyComputes run := candidates_computes.comp RationalMin.run_computes
end MetricKMedianRecovery.BitMachine.BinaryPopulation

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletion
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)

attribute [local irreducible] mapWith
noncomputable def cap_computes : PolyComputes cap :=
  (cons_computes (discardPrefix_computes.comp (field_computes 0)) offers_computes).comp RationalMin.run_computes
attribute [local irreducible] RationalMin.run
noncomputable def weightedCap_computes : PolyComputes weightedCap :=
  RatOps.mul (RatOps.ofWords (discardPrefix_computes.comp extractPrefix_computes))
    (RatOps.ofWords ((extractPrefix_computes.pair (discardPrefix_computes.comp discardPrefix_computes)).comp cap_computes))
end MetricKMedianRecovery.BitMachine.BinaryCompletion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueChoice
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueChoice
open WordOperations WordList BinaryArithmetic
variable {A : Type*}
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [Function.comp_def,decide_eq_true_eq] using
   (extractPrefix_computes.comp isEmpty_computes).cond discardPrefix_computes
    ((discardPrefix_computes.comp isEmpty_computes).cond extractPrefix_computes
      ((RatOps.le (RatOps.ofWords (extractPrefix_computes.comp score_computes))
        (RatOps.ofWords (discardPrefix_computes.comp score_computes))).cond extractPrefix_computes discardPrefix_computes))
noncomputable def step_computes : PolyComputes step := (Fold.accum_computes.pair Find.item_computes).comp run_computes
noncomputable def select_computes : PolyComputes select :=
  (id_computes.pair (Fold.pack_computes id_computes (const_computes []) (const_computes []))).comp (CappedFold.run_computes step_computes)

end MetricKMedianRecovery.BitMachine.BinaryBlueChoice

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
attribute [local irreducible] mapWith
noncomputable def run (d : ℕ) (x : List Bool) : List Bool := BinaryMetricBest.run
  (pairBits (metricContext x,pairBits (field 3 x,candidateWords d x)))
attribute [local irreducible] metricContext candidateWords
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
noncomputable def atOption (d : ℕ) (x : List Bool) : List Bool :=
  if decide (discardPrefix x=[]) then src 3 x else run d (replaceState x)
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
noncomputable def index (x : List Bool) : List Bool := BinaryDyadic.run (encode [field 2 x,weights x,(0:ℕ).bits,field 3 x])
noncomputable def run (x : List Bool) : List Bool := Lookup.run (pairBits (index x,actions x))
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

noncomputable def step (x : List Bool) : List Bool := Update.run (pairBits (input x,Draw.run (drawInput x)))
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
noncomputable def run (x : List Bool) : List Bool :=
  CappedFold.run step (pairBits (cap.word x,Fold.pack (field 3 x) (fixedContext x) initial))
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
noncomputable def prefixBits (x : List Bool) : List Bool :=
  Take.run (pairBits (discardPrefix x,field 3 (extractPrefix x)))
noncomputable def atPrefix (x : List Bool) : List Bool := Loop.run
  (encode [field 0 (extractPrefix x),field 1 (extractPrefix x),field 2 (extractPrefix x),prefixBits x])
noncomputable def run (x : List Bool) : List Bool :=
  mapWith atPrefix (pairBits (input x,BinaryEllipsoidInitial.indices (field 2 x++[true])))
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
noncomputable def candidateWords (d : ℕ) (x : List Bool) : List Bool :=
  mapWith (BinaryRecovery.atOption d) (pairBits (recoveryContext x,BinarySampler.Trace.run (sampleContext x)))
attribute [local irreducible] mapWith recoveryContext sampleContext BinarySampler.Trace.run
noncomputable def run (d : ℕ) (x : List Bool) : List Bool :=
  BinaryMetricBest.run (pairBits (metricContext x,pairBits (src 4 x,candidateWords d x)))
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
noncomputable def run (d : ℕ) : List Bool→List Bool := BinaryIntegralRecovery.run d ∘ repack
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
noncomputable def atSeed (d : ℕ) : List Bool→List Bool := Fair.run d ∘ atSeedInput
noncomputable def candidates (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  mapWith (atSeed d) (pairBits (context x,rows Q x))
attribute [local irreducible] mapWith
noncomputable def run (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  BinaryMetricBest.run (pairBits (metricContext x,pairBits (src 4 x,candidates Q d x)))
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
noncomputable def run (Q : Polynomial ℕ) (d : ℕ) : List Bool→List Bool := Repeat.run Q d ∘ cut Q
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
noncomputable def atChoice (Q : Polynomial ℕ) (d : ℕ) : List Bool→List Bool := Repeat.FiniteTape.run Q d ∘ atInput
noncomputable def candidateWords (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  mapWith (atChoice Q d) (pairBits (x,choices x))
attribute [local irreducible] mapWith
noncomputable def runInput (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  encode [src 0 x,src 2 x,src 3 x,src 4 x,sizeWord x,candidateWords Q d x]
attribute [local irreducible] sizeWord candidateWords
noncomputable def run (Q : Polynomial ℕ) (d : ℕ) : List Bool→List Bool := BinarySanitizedBest.run ∘ runInput Q d
variable {n : ℕ}
noncomputable def words (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n))
    (Δ : ℕ) (g raw : List Bool) : List (List Bool) :=
  (List.ofFn (fun p:Fin (D.card*Δ+1)=>p)).flatMap (fun p=>List.ofFn (fun m:Fin (n+1)=>
    Repeat.FiniteTape.run Q d (Fair.pack δ D F S Δ p.val m.val g raw)))
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoverySelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses
open Completion Sampling Sampling.Comparison FiniteSampling
variable {n : ℕ}
noncomputable def output (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℕ) (g raw : List Bool) : Finset (Fin n) :=
  BinarySanitizedBest.output δ D F S S.card (words Q d δ D F S Δ g raw)
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
namespace R
noncomputable abbrev run := BinaryIntegralRecovery.Guesses.run
end R
variable {n : ℕ}
attribute [local irreducible] bare RawTake.run UnaryResources.lengthBits BinaryIntegralRecovery.Guesses.run
attribute [local irreducible] mapWith
noncomputable def start (x : List Bool) : List Bool := anchor (pairBits (x,field 5 x))
attribute [local irreducible] start
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
noncomputable def matrix (x : List Bool) : List Bool := BinaryInputParser.Metric.matrix (raw x)
noncomputable def prep (x : List Bool) : List Bool := encode [matrix x,points x,clientCount x,discardPrefix x]
noncomputable def rounded (x : List Bool) : List Bool := BinaryNormalization.run (prep x)
noncomputable def mesh (x : List Bool) : List Bool := BinaryNormalization.mesh (prep x)
noncomputable def cap (x : List Bool) : List Bool := BinaryNormalization.cap (prep x)
noncomputable def run (x : List Bool) : List Bool := encode [rounded x,twice x,clients x,facilities x,budget x,mesh x,cap x]
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
noncomputable def norm : List Bool→List Bool := BinaryNormalizeInput.run ∘ normInput
noncomputable def src (j : ℕ) : List Bool→List Bool := field j ∘ norm
noncomputable def fcount : List Bool→List Bool := UnaryResources.lengthBits ∘ Count.run ∘ src 3
noncomputable def clamp (x : List Bool) : List Bool := (min (value (src 4 x)) (value (fcount x))).bits
noncomputable def base (x : List Bool) : List Bool :=
  encode [src 0 x,src 1 x,src 2 x,src 3 x,src 6 x,clamp x,field 0 x,[]]
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
namespace P
noncomputable abbrev matrix := BinaryInputParser.Metric.matrix
end P
noncomputable def fallback : List Bool→List Bool := BinaryCompletionPad.run ∘ fallbackInput
noncomputable def zeroInput (x : List Bool) : List Bool := encode [P.matrix x,P.clients x,P.facilities x]
noncomputable def zero : List Bool→List Bool := BinaryGlobalZero.run ∘ zeroInput
attribute [local irreducible] BinaryInputParser.Metric.matrix BinaryNormalizeInput.P.clients
  BinaryNormalizeInput.P.facilities BinaryInputParser.Metric.budget fallback
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end


