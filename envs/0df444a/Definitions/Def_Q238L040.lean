-- Prove2me | Definitions.Def_Q238L040
-- name    : Q238L040
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:39:11.728189+00:00
-- url     : https://prove2.me/theorems/d4d43a50-3558-4f35-a0d9-480974db880a
-- title:
--   Definitions bundle Q238L040 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 41 declarations of OpenAI's Lean: 41 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueChoice.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueChoice.select_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueChoice.step_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.contents_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.result_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.marginalDraw_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.marginalValues_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.marginal_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.score_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.cap_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.weightedCap_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.R.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.start`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.demandBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.atChoice`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.candidateWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.output`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.runInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.words`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.atSeed`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.candidates`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.rows`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.candidateWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseAdvance.budgetItem_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseAdvance.budget_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseAdvance.clippedItem_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseAdvance.isActive_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseAdvance.nearest_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseAdvance.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPopulation.near_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atOption`, `OAI.MetricKMedianRecovery.BitMachine.BinarySanitizedBest.candidates`, `OAI.MetricKMedianRecovery.BitMachine.BinarySanitizedBest.run` and 1 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_CandidateSanitize`, `KMedianRecovery_Algorithms_IntegralRecoveryAll`, `KMedianRecovery_Algorithms_IntegralRecoveryAmplified`, `KMedianRecovery_Algorithms_IntegralRecoveryDemand`, `KMedianRecovery_Algorithms_IntegralRecoveryGuesses`, `KMedianRecovery_Algorithms_IntegralRecoveryMachine`, `KMedianRecovery_Algorithms_IntegralRecoveryRepeat`, `KMedianRecovery_Algorithms_IntegralRecoverySelection`, `KMedianRecovery_Algorithms_IntegralRecoverySuccess`, `KMedianRecovery_Branching_BlueChoice`, `KMedianRecovery_Branching_BlueMerge`, `KMedianRecovery_Branching_CategoricalScore`, `KMedianRecovery_Branching_CategoricalTable`, `KMedianRecovery_Branching_PopulationMachine`, `KMedianRecovery_Encoding_RationalCap`, `KMedianRecovery_Machines_RecoveryOptionMachine`, `KMedianRecovery_Recovery_Min`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L036`, `Q238L037` and `Q238L038` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L041`, `Q238L042`, `Q238L043` and `Q238L046`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.run_source_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.cost_le_designated_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.integral_recovery_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.polynomial_recovery_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.run_output_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.polynomial_program_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.run_source_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atOption_none_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.run_source_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.cost_le_designated_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.integral_recovery_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.polynomial_recovery_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.run_output_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.polynomial_program_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.run_source_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atOption_none_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L036
import Definitions.Def_Q238L037
import Definitions.Def_Q238L038

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
end MetricKMedianRecovery.BitMachine.BinaryPopulation

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {E : Type*} {a T : ℕ}
noncomputable def draw_computes : PolyComputes draw := (id_computes.pair drawItems_computes).comp (flatMapWith_computes drawPick_computes)
attribute [local irreducible] Set.run mapWith
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalScore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
noncomputable def marginalDraw_computes : PolyComputes marginalDraw :=
  (cons_computes ((extractPrefix_computes.comp extractPrefix_computes).comp (field_computes 1))
    (cons_computes discardPrefix_computes (cons_computes (extractPrefix_computes.comp elementPart_computes)
      (const_computes [])))).comp draw_computes
noncomputable def marginal_computes {g : List Bool→List Bool} (hg : PolyComputes g) : PolyComputes (marginal g) :=
  RatOps.sub (RatOps.ofWords ((((extractPrefix_computes.comp extractPrefix_computes).comp (field_computes 0)).pair
    (cons_computes (extractPrefix_computes.comp discardPrefix_computes) marginalDraw_computes)).comp hg))
    (RatOps.ofWords ((((extractPrefix_computes.comp extractPrefix_computes).comp (field_computes 0)).pair
      marginalDraw_computes).comp hg))
attribute [local irreducible] mapWith
noncomputable def marginalValues_computes {g : List Bool→List Bool} (hg : PolyComputes g) : PolyComputes (marginalValues g) := by
  unfold marginalValues
  exact (id_computes.pair elementSamples_computes).comp (mapWith_computes (marginal_computes hg))
noncomputable def score_computes {g : List Bool→List Bool} (hg : PolyComputes g) : PolyComputes (score g) :=
  RatOps.div (RatOps.ofWords ((marginalValues_computes hg).comp RationalArray.sumWords_computes))
    (RatOps.nat ((elementSamples_computes.comp Count.run_computes).comp UnaryResources.lengthBits_computes))
end MetricKMedianRecovery.BitMachine.BinaryCategorical

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
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_CandidateSanitize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySanitizedBest
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def candidates (x : List Bool) : List Bool := mapWith atRaw (pairBits (sanitizeContext x,field 5 x))
noncomputable def run (x : List Bool) : List Bool := BinaryMetricBest.run
  (pairBits (metricContext x,pairBits (field 3 x,candidates x)))
end MetricKMedianRecovery.BitMachine.BinarySanitizedBest

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
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueMerge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueCollect
open WordOperations WordList
variable {A : Type*}
attribute [local irreducible] mapWith
noncomputable def contents_computes : PolyComputes contents := ((const_computes []).pair id_computes).comp (flatMapWith_computes payloadOp_computes)
noncomputable def result_computes : PolyComputes result :=
  cons_computes ((scores_computes.comp RationalArray.sumWords_computes).pair contents_computes) (const_computes [])
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [Function.comp_def,decide_eq_true_eq] using
    (bad_computes.comp isEmpty_computes).cond result_computes (const_computes [])
end MetricKMedianRecovery.BitMachine.BinaryBlueCollect

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
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryDemand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
open WordOperations Polynomial
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def demandBits : List Bool→List Bool := UnaryResources.lengthBits ∘ demandWord
attribute [local irreducible] extra raw demandBits RawTake.run
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
noncomputable def rows (Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  BinarySeed.rows (pairBits (encode [rword Q x,bword x],Fair.raw x))
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


