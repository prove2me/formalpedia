-- Prove2me | Definitions.Def_Q238L045
-- name    : Q238L045
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:43:58.5507+00:00
-- url     : https://prove2.me/theorems/c0ef267c-51d7-4d51-b31b-876a295ba8e9
-- title:
--   Definitions bundle Q238L045 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 119 declarations of OpenAI's Lean: 119 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.count_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.counts_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.power_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.prepared_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.scale_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.far_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.high_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.unaryRat`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.context_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.initialInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.low_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.sizeRat`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.size_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.threshold_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.total_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.R.budget`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.counter`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.demand`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.demands`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.src_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.completionWord_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.demandWord_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.raw_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.sampleWord_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.atDemand_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.atInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.atParams_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.budget`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.choices_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.costRange_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.costWord_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.countRange_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.count_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.demandWords_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.price_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.source_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape.demandWord_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.bword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.rword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.extra_computes` and 79 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_IntegralRecoveryAll`, `KMedianRecovery_Algorithms_IntegralRecoveryAmplified`, `KMedianRecovery_Algorithms_IntegralRecoveryDemand`, `KMedianRecovery_Algorithms_IntegralRecoveryGuesses`, `KMedianRecovery_Algorithms_IntegralRecoveryMachine`, `KMedianRecovery_Algorithms_IntegralRecoveryRepeat`, `KMedianRecovery_Algorithms_IntegralRecoverySelection`, `KMedianRecovery_Algorithms_IntegralRecoverySuccess`, `KMedianRecovery_Encoding_LengthEncode`, `KMedianRecovery_Geometry_LocalBest`, `KMedianRecovery_Geometry_LocalCandidates`, `KMedianRecovery_Geometry_LocalRefineMachine`, `KMedianRecovery_Geometry_LocalSets`, `KMedianRecovery_Machines_InitialLoop`, `KMedianRecovery_Machines_LengthQuery`, `KMedianRecovery_Machines_ProjectionMachine`, `KMedianRecovery_Machines_SensitiveMachine`, `KMedianRecovery_Recovery_InitialAuto`, `KMedianRecovery_Recovery_InitialCorrect`, `KMedianRecovery_Recovery_LengthCandidates`, `KMedianRecovery_Recovery_PlanResult`, `KMedianRecovery_Sampling_InverseCDF`, `KMedianRecovery_Sampling_SamplerParameters`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundle `Q238L039` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L049` and `Q238L050`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.all_counts_budget_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.integral_recovery_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.polynomial_recovery_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.all_counts_budget_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.integral_recovery_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.polynomial_recovery_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L039

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_InverseCDF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.RatOps
noncomputable def natFloor {f : List Bool→ℚ} (hf : PolyComputes (fun x=>BinaryRational.encode (f x))) :
    PolyComputes (fun x=>(⌊f x⌋₊).bits) := by
  have hh := (hf.comp BinaryRational.floorWords_computes).comp Signed.natWords_computes
  simpa only [Function.comp_def,BinaryRational.floorWords_encode,Signed.natWords_encode,Int.floor_toNat] using hh
end MetricKMedianRecovery.BitMachine.RatOps

namespace MetricKMedianRecovery.BitMachine.BinaryDyadic
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def power_computes : PolyComputes power := by
  have hh:=UnaryResources.copy_computes id_computes (const_computes [false])
  have he : PolyComputes (fun x : List Bool=>List.replicate x.length false) := by
    simpa only [id_eq,RawUnary.copies_singleton] using hh
  exact he.append (const_computes [true])
noncomputable def scale_computes : PolyComputes (fun x=>BinaryRational.encode (scale x)) := RatOps.nat power_computes
noncomputable def count_computes : PolyComputes count :=
  RatOps.natFloor (RatOps.mul (RatOps.ofWords discardPrefix_computes) (RatOps.ofWords extractPrefix_computes))
noncomputable def counts_computes : PolyComputes counts := by
  have computation := (((field_computes 0).comp scale_computes).pair (field_computes 1)).comp (mapWith_computes count_computes)
  unfold counts
  simpa only [Function.comp_def] using computation
noncomputable def prepared_computes : PolyComputes prepared :=
  cons_computes (field_computes 2) (cons_computes counts_computes (cons_computes (field_computes 3) (const_computes [])))
end MetricKMedianRecovery.BitMachine.BinaryDyadic

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Parameters
open WordOperations WordList BinaryArithmetic Polynomial RadiusMenus Sampling Sampling.Comparison
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BoundedNatWord.run bound
noncomputable def unary_computes (j : ℕ) : PolyComputes (unary j) :=
  ((field_computes j).pair id_computes).comp (BoundedNatWord.run_computes bound)
noncomputable def Jword_computes : PolyComputes Jword :=
  (const_computes [true]).append (UnaryResources.copy_computes (unary_computes 7) (const_computes (List.replicate 2000000 true)))
noncomputable def nword_computes : PolyComputes nword := (field_computes 2).comp Count.run_computes
noncomputable def precision_computes : PolyComputes precision :=
  (((nword_computes.append (unary_computes 5)).append (const_computes (List.replicate M true))).append
    (const_computes (List.replicate E true))).append Jword_computes |>.append (const_computes (List.replicate 5 true))
end MetricKMedianRecovery.BitMachine.BinarySampler.Parameters

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
noncomputable def src_computes (j : ℕ) : PolyComputes (src j) := extractPrefix_computes.comp (field_computes j)
noncomputable def extra_computes : PolyComputes extra := discardPrefix_computes.comp extractPrefix_computes
noncomputable def mword_computes : PolyComputes mword := extractPrefix_computes.comp (BinarySampler.Parameters.unary_computes 7)
noncomputable def precision_computes : PolyComputes precision := extractPrefix_computes.comp BinarySampler.Parameters.precision_computes
attribute [local irreducible] src mword extra completeRaw BinaryRational.natWords
attribute [local irreducible] mapWith recoveryContext sampleContext
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
noncomputable def raw_computes : PolyComputes raw := discardPrefix_computes.comp discardPrefix_computes
attribute [local irreducible] mword precision sampleCount raw extra RawTake.run RawDrop.run
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
noncomputable def sampleWord_computes : PolyComputes sampleWord := UnaryResources.copy_computes
  (mword_computes.append mword_computes) precision_computes
noncomputable def completionWord_computes : PolyComputes completionWord := (src_computes 1).comp completionCounter.computes
noncomputable def demandWord_computes : PolyComputes demandWord := sampleWord_computes.append completionWord_computes
attribute [local irreducible] extra raw RawTake.run
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
attribute [local irreducible] extra Fair.raw Fair.demandWord BinaryMetricBest.run RawUnary.run BinaryIntegralRecovery.result BinaryFinSet.encode BinarySampler.Parameters.pack BinaryMetricBest.best Fair.output List.ofFn BinarySeed.raw
noncomputable def rword_computes (Q : Polynomial ℕ) : PolyComputes (rword Q) :=
  (extra_computes.comp (counter Q).computes).comp RawUnary.run_computes
noncomputable def bword_computes : PolyComputes bword := Fair.demandWord_computes.comp RawUnary.run_computes
attribute [local irreducible] mapWith
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
attribute [local irreducible] Fair.pack Fair.raw Repeat.rword Repeat.bword RawTake.run extra
noncomputable def demandWord_computes (Q : Polynomial ℕ) : PolyComputes (demandWord Q) :=
  UnaryResources.copy_computes (Repeat.rword_computes Q) Repeat.bword_computes
attribute [local irreducible] demandBits
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
attribute [local irreducible] BinaryFinSet.encode BinarySampler.Parameters.unary Count.run src
noncomputable def costWord_computes : PolyComputes costWord := UnaryResources.copy_computes
  ((src_computes 2).comp Count.run_computes) (extractPrefix_computes.comp (BinarySampler.Parameters.unary_computes 5))
noncomputable def costRange_computes : PolyComputes costRange :=
  (costWord_computes.append (const_computes _)).comp BinaryEllipsoidInitial.indices_computes
noncomputable def countRange_computes : PolyComputes countRange :=
  ((src_computes 1).append (const_computes _)).comp BinaryEllipsoidInitial.indices_computes
noncomputable def choices_computes : PolyComputes choices := (costRange_computes.pair countRange_computes).comp cross_computes
noncomputable def source_computes (j : ℕ) : PolyComputes (source j) := extractPrefix_computes.comp (src_computes j)
noncomputable def price_computes : PolyComputes price :=
  (discardPrefix_computes.comp extractPrefix_computes).comp BinaryRational.natWords_computes
noncomputable def count_computes : PolyComputes count := discardPrefix_computes.comp discardPrefix_computes
noncomputable def atParams_computes : PolyComputes atParams := list_computes
  [source 0,source 1,source 2,source 3,source 4,source 5,price,count] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨source_computes _⟩ | exact ⟨price_computes⟩ | exact ⟨count_computes⟩)
noncomputable def atInput_computes : PolyComputes atInput := atParams_computes.pair
  ((extractPrefix_computes.comp extra_computes).pair (extractPrefix_computes.comp Fair.raw_computes))
attribute [local irreducible] mapWith
attribute [local irreducible] sizeWord
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
open WordOperations WordList
attribute [local irreducible] atInput choices Repeat.FiniteTape.demandWord
noncomputable def atDemand_computes (Q : Polynomial ℕ) : PolyComputes (atDemand Q) :=
  atInput_computes.comp (Repeat.FiniteTape.demandWord_computes Q)
attribute [local irreducible] mapWith
noncomputable def demandWords_computes (Q : Polynomial ℕ) : PolyComputes (demandWords Q) :=
  PolyComputes.comp (f := fun input=>pairBits (input,choices input)) (g := mapWith (atDemand Q))
    (id_computes.pair choices_computes) (mapWith_computes (atDemand_computes Q))
noncomputable def budget (Q : Polynomial ℕ) : Polynomial ℕ := (demandWords_computes Q).lengthPolynomial
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LengthEncode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLength
open WordOperations WordList RationalLeaves CanonicalLengthView BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryLabelMatrix.row
noncomputable def cf_computes (n : ℕ) : PolyComputes (cf n) := extractPrefix_computes.comp (field_computes n)
noncomputable def pf_computes (n : ℕ) : PolyComputes (pf n) := discardPrefix_computes.comp (field_computes n)
noncomputable def isFree_computes : PolyComputes (fun x=>[isFree x]) := by
  simpa only [isFree,value_bits] using NatOps.eq (pf_computes 0) (const_computes (0:ℕ).bits)
noncomputable def source_computes : PolyComputes source := isFree_computes.cond (cf_computes 2)
  ((pf_computes 3).append (cons_computes (pf_computes 1) (pf_computes 4)))
noncomputable def target_computes : PolyComputes target := isFree_computes.cond
  ((cf_computes 2).append (cons_computes (pf_computes 2) (const_computes [])))
  ((pf_computes 3).append (pf_computes 4))
noncomputable def rootIn_computes : PolyComputes (fun x=>[rootIn x]) :=
  ((pf_computes 1).pair (cf_computes 0)).comp BinaryLabel.contains_computes
noncomputable def freeOut_computes : PolyComputes (fun x=>[freeOut x]) :=
  (((pf_computes 2).pair (cf_computes 0)).comp BinaryLabel.contains_computes).not
noncomputable def row_computes (n : ℕ) : PolyComputes (row n) :=
  ((cf_computes 4).pair (pf_computes n)).comp BinaryLabelMatrix.row_computes
end MetricKMedianRecovery.BitMachine.BinaryLength

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LengthQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLengthQuery
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def cf_computes (n : ℕ) : PolyComputes (cf n) := extractPrefix_computes.comp (field_computes n)
noncomputable def newLeaf_computes : PolyComputes newLeaf := by
  have hi : PolyComputes (fun x=>(value (cf 3 x)+1).bits) := by
    simpa only [value_bits] using NatOps.add (cf_computes 3) (const_computes (1:ℕ).bits)
  exact hi.pair (((cf_computes 4).comp BinaryLabel.parentWords_computes).pair discardPrefix_computes)
noncomputable def opened_computes : PolyComputes opened :=
  (((cf_computes 0).comp (field_computes 3)).pair (cons_computes newLeaf_computes (const_computes []))).comp
    BinaryFiniteContext.union_computes
noncomputable def base_computes : PolyComputes base := ((cf_computes 0).pair opened_computes).comp BinaryFiniteContext.replaceOpen_computes
noncomputable def isZero_computes : PolyComputes (fun x=>[isZero x]) := RatOps.eq (RatOps.ofWords discardPrefix_computes) (RatOps.const 0)
noncomputable def isUpper_computes : PolyComputes (fun x=>[isUpper x]) := RatOps.eq (RatOps.ofWords discardPrefix_computes) (RatOps.ofWords (cf_computes 5))
end MetricKMedianRecovery.BitMachine.BinaryLengthQuery

namespace MetricKMedianRecovery.BitMachine.BinaryLengthSearch
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def lower_computes : PolyComputes lower := discardPrefix_computes.comp extractPrefix_computes
noncomputable def upper_computes : PolyComputes upper := discardPrefix_computes.comp discardPrefix_computes
noncomputable def context_computes : PolyComputes context := extractPrefix_computes.comp (field_computes 1)
noncomputable def boundK_computes : PolyComputes boundK := extractPrefix_computes.comp (field_computes 2)
noncomputable def leftInput_computes : PolyComputes leftInput := context_computes.pair lower_computes
noncomputable def rightInput_computes : PolyComputes rightInput := context_computes.pair upper_computes
end MetricKMedianRecovery.BitMachine.BinaryLengthSearch

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
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def jf_computes (n : ℕ) : PolyComputes (jf n) := (field_computes 10).comp (field_computes n)
noncomputable def isFree_computes : PolyComputes (fun x=>[isFree x]) := by
  simpa only [isFree,value_bits] using NatOps.eq (jf_computes 0) (const_computes (0:ℕ).bits)
noncomputable def common_computes : PolyComputes common := isFree_computes.cond (field_computes 7) ((jf_computes 3).append (jf_computes 4))
noncomputable def small_computes : PolyComputes small := isFree_computes.cond (field_computes 9) (field_computes 8)
noncomputable def large_computes : PolyComputes large := isFree_computes.cond (field_computes 8) (field_computes 9)
noncomputable def opened_computes : PolyComputes opened :=
  (((field_computes 0).comp (field_computes 3)).pair common_computes).comp BinaryFiniteContext.union_computes
noncomputable def base_computes : PolyComputes base := ((field_computes 0).pair opened_computes).comp BinaryFiniteContext.replaceOpen_computes
noncomputable def nextQ_computes : PolyComputes nextQ := (const_computes [true]).append (field_computes 2)
noncomputable def context_computes : PolyComputes context :=
  list_computes [base,field 1,nextQ,field 3,jf 1,field 4,small,large] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨base_computes⟩
    · exact ⟨field_computes 1⟩
    · exact ⟨nextQ_computes⟩
    · exact ⟨field_computes 3⟩
    · exact ⟨jf_computes 1⟩
    · exact ⟨field_computes 4⟩
    · exact ⟨small_computes⟩
    · exact ⟨large_computes⟩)
noncomputable def searchInput_computes : PolyComputes searchInput :=
  list_computes [field 6,context,field 5,(fun _=>BinaryRational.encode 0),field 4] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    · exact ⟨field_computes 6⟩
    · exact ⟨context_computes⟩
    · exact ⟨field_computes 5⟩
    · exact ⟨const_computes (BinaryRational.encode 0)⟩
    · exact ⟨field_computes 4⟩)
noncomputable def atZero_computes : PolyComputes atZero := context_computes.pair (const_computes (BinaryRational.encode 0))
noncomputable def early_computes : PolyComputes early :=
  cons_computes (const_computes (0:ℕ).bits) (cons_computes (const_computes (BinaryRational.encode 0))
    (cons_computes (const_computes []) (cons_computes small_computes (cons_computes (const_computes []) (const_computes [])))))
end MetricKMedianRecovery.BitMachine.BinarySensitive

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalSets
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def addOne_computes : PolyComputes addOne :=
  (cons_computes extractPrefix_computes discardPrefix_computes).comp BinaryLabel.sort_computes
noncomputable def without_computes : PolyComputes (fun x=>[without x]) :=
  (swapWords_computes.comp BinaryLabel.contains_computes).not
noncomputable def diff_computes : PolyComputes diff :=
  (swapWords_computes.comp (filterWith_computes without_computes)).comp BinaryLabel.sort_computes
noncomputable def insertEach_computes : PolyComputes insertEach := swapWords_computes.comp (mapWith_computes addOne_computes)
end MetricKMedianRecovery.BitMachine.BinaryLocalSets

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalCandidates
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryLocalSets
noncomputable def widths_computes (w : ℕ) : PolyComputes (widths w) := by
  induction w with
  | zero=>exact const_computes _
  | succ w ih=>
    unfold widths
    have computes := ih.append ((ih.pair id_computes).comp (flatMapWith_computes insertEach_computes))
    simpa only [Function.comp_def,id_eq] using computes
noncomputable def sameSize_computes : PolyComputes (fun x=>[sameSize x]) :=
  NatOps.eq (extractPrefix_computes.comp size_computes) (discardPrefix_computes.comp size_computes)
noncomputable def removed_computes (w : ℕ) : PolyComputes (removed w) := by
  unfold removed
  have computes := (discardPrefix_computes.pair (extractPrefix_computes.comp (widths_computes w))).comp (mapWith_computes diff_computes)
  simpa only [Function.comp_def] using computes
noncomputable def raw_computes (w : ℕ) : PolyComputes (raw w) :=
  ((removed_computes w).pair (extractPrefix_computes.comp (widths_computes w))).comp
    (crossWith_computes BinaryFiniteContext.union_computes)
noncomputable def run_computes (w : ℕ) : PolyComputes (run w) :=
  (discardPrefix_computes.pair (raw_computes w)).comp (filterWith_computes sameSize_computes)
end MetricKMedianRecovery.BitMachine.BinaryLocalCandidates

namespace MetricKMedianRecovery.BitMachine.BinaryLocalCost
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def entry_computes : PolyComputes entry :=
  (((extractPrefix_computes.comp extractPrefix_computes).pair discardPrefix_computes).pair
    (extractPrefix_computes.comp discardPrefix_computes)).comp BinaryLabel.row_computes
noncomputable def near_computes : PolyComputes near := by
  unfold near
  have computes := ((((extractPrefix_computes.comp (field_computes 0)).pair discardPrefix_computes).pair
    (extractPrefix_computes.comp (field_computes 2))).comp (mapWith_computes entry_computes)).comp RationalMin.run_computes
  simpa only [Function.comp_def] using computes
noncomputable def run_computes : PolyComputes run := by
  unfold run
  have computes := ((id_computes.pair ((field_computes 1).comp BinaryEllipsoidInitial.indices_computes)).comp
    (mapWith_computes near_computes)).comp RationalArray.sumWords_computes
  simpa only [Function.comp_def,id_eq] using computes
noncomputable def rank_computes : PolyComputes rank := RatOps.natCeil (RatOps.ofWords run_computes)
end MetricKMedianRecovery.BitMachine.BinaryLocalCost

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalBest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalBest
open WordOperations WordList BinaryArithmetic
noncomputable def choose_computes {rank : List Bool→List Bool} (hr : PolyComputes rank) : PolyComputes (choose rank) := by
  have h := (NatOps.lt ((Find.context_computes.pair Find.item_computes).comp hr)
    ((Find.context_computes.pair Fold.accum_computes).comp hr)).cond Find.item_computes Fold.accum_computes
  unfold choose
  simpa only [decide_eq_true_eq,Function.comp_def] using h
noncomputable def run_computes {rank : List Bool→List Bool} (hr : PolyComputes rank) : PolyComputes (run rank) :=
  (id_computes.pair (Fold.pack_computes (discardPrefix_computes.comp discardPrefix_computes) extractPrefix_computes
    (discardPrefix_computes.comp extractPrefix_computes))).comp (CappedFold.run_computes (choose_computes hr))
end MetricKMedianRecovery.BitMachine.BinaryLocalBest

namespace MetricKMedianRecovery.BitMachine.BinaryLocalSearch
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def rank_computes : PolyComputes rank :=
  (list_computes [field 0 ∘ extractPrefix,field 1 ∘ extractPrefix,discardPrefix] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨extractPrefix_computes.comp (field_computes 0)⟩
    · exact ⟨extractPrefix_computes.comp (field_computes 1)⟩
    · exact ⟨discardPrefix_computes⟩)).comp BinaryLocalCost.rank_computes
noncomputable def selected_computes (w : ℕ) : PolyComputes (selected w) :=
  (id_computes.pair ((field_computes 3).pair (((field_computes 2).pair (field_computes 3)).comp
    (BinaryLocalCandidates.run_computes w)))).comp (BinaryLocalBest.run_computes rank_computes)
noncomputable def step_computes (w : ℕ) : PolyComputes (step w) := list_computes
  [field 0,field 1,field 2,selected w] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl
    all_goals first | exact ⟨field_computes _⟩ | exact ⟨selected_computes w⟩)
end MetricKMedianRecovery.BitMachine.BinaryLocalSearch

namespace MetricKMedianRecovery.BitMachine.BinaryLocalSearch
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def iterationInput_computes : PolyComputes iterationInput :=
  extractPrefix_computes.pair (capacity.computes.pair discardPrefix_computes)
noncomputable def run_computes (w : ℕ) : PolyComputes (run w) :=
  iterationInput_computes.comp ((BoundedIteration.run_computes (step_computes w)).comp (field_computes 3))
end MetricKMedianRecovery.BitMachine.BinaryLocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ProjectionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryProjection
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
noncomputable def originalWord_computes : PolyComputes originalWord :=
  (const_computes _).pair (id_computes.pair (const_computes _))
noncomputable def lift_computes : PolyComputes lift :=
  (map_computes originalWord_computes).comp BinaryLabel.sort_computes
end MetricKMedianRecovery.BitMachine.BinaryProjection

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
noncomputable abbrev budget := BinaryIntegralRecovery.Guesses.budget
end R
variable {n : ℕ}
noncomputable def src_computes (j : ℕ) : PolyComputes (src j) := extractPrefix_computes.comp (field_computes j)
noncomputable def counter (Q : Polynomial ℕ) : PolynomialCounter (R.budget Q) := PolynomialCounter.choose _
noncomputable def demand (Q : Polynomial ℕ) : List Bool→List Bool := (counter Q).word ∘ bare
attribute [local irreducible] counter demand bare RawTake.run UnaryResources.lengthBits BinaryIntegralRecovery.Guesses.budget
attribute [local irreducible] mapWith
noncomputable def demands (Q : Polynomial ℕ) (x : List Bool) : List Bool := mapWith (demand Q) (pairBits (x,ranks x))
end MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalRefineMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalRefine
open RationalLeaves WordOperations WordList Polynomial
noncomputable def run_computes : PolyComputes run :=
  (BinaryLocalAnchor.fuel.computes.pair id_computes).comp (BinaryLocalSearch.run_computes 5)
end MetricKMedianRecovery.BitMachine.BinaryLocalRefine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLength
open WordOperations WordList RationalLeaves CanonicalLengthView BinaryArithmetic CanonicalMergeRefinement
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] WordList.mapWith
noncomputable def freeOp_computes : PolyComputes freeOp :=
  list_computes [fun _=>(0:ℕ).bits,extractPrefix,discardPrefix,fun _=>[],fun _=>[]] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    · exact ⟨const_computes _⟩
    · exact ⟨extractPrefix_computes⟩
    · exact ⟨discardPrefix_computes⟩
    · exact ⟨const_computes _⟩
    · exact ⟨const_computes _⟩)
noncomputable def paidOp_computes : PolyComputes paidOp :=
  list_computes [fun _=>(1:ℕ).bits,pf 1,fun _=>[],pf 0,pf 2] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    · exact ⟨const_computes _⟩
    · exact ⟨pf_computes _⟩
    · exact ⟨const_computes _⟩
    · exact ⟨pf_computes _⟩
    · exact ⟨pf_computes _⟩)
noncomputable def frees_computes : PolyComputes frees :=
  ((field_computes 1).pair (field_computes 3)).comp (crossWith_computes freeOp_computes)
noncomputable def paids_computes : PolyComputes paids :=
  ((const_computes []).pair ((field_computes 2).comp Slices.run_computes)).comp (mapWith_computes paidOp_computes)
noncomputable def candidates_computes : PolyComputes candidates := frees_computes.append paids_computes
end MetricKMedianRecovery.BitMachine.BinaryLength

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_PlanResult
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPlanResult
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge CanonicalLengthView
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

noncomputable def rf_computes (n : ℕ) : PolyComputes (rf n) := (field_computes 3).comp (field_computes n)
noncomputable def success_computes : PolyComputes (fun x=>[success x]) := by
  simpa only [success,value_bits] using NatOps.eq (rf_computes 0) (const_computes (0:ℕ).bits)
noncomputable def rightHeight_computes : PolyComputes rightHeight := success_computes.cond (rf_computes 1) (rf_computes 2)
noncomputable def common_computes : PolyComputes common := (field_computes 0).comp BinarySensitive.common_computes
end MetricKMedianRecovery.BitMachine.BinaryPlanResult

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_InitialLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitial
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outputBits)
attribute [local irreducible] BinaryBisection.run
noncomputable def unaryRat {f : List Bool→List Bool} (hf : PolyComputes f) :
    PolyComputes (fun x=>BinaryRational.encode ((f x).length:ℚ)) := by
  simpa only [Function.comp_def,UnaryResources.lengthBits_eq,value_bits] using RatOps.nat (hf.comp UnaryResources.lengthBits_computes)
noncomputable def high_computes : PolyComputes high :=
  RatOps.mul (RatOps.mul (RatOps.const 8) (unaryRat ((field_computes 0).comp (field_computes 1))))
    (RatOps.ofWords (field_computes 6))
noncomputable def far_computes : PolyComputes far :=
  RatOps.mul (RatOps.mul (RatOps.const 20) (unaryRat (field_computes 1))) (RatOps.ofWords (field_computes 6))

end MetricKMedianRecovery.BitMachine.BinaryInitial

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFuel
open WordOperations BinaryArithmetic RationalPhaseFuel RationalHeight

noncomputable def threshold_computes : PolyComputes (fun x=>BinaryRational.encode (threshold x)) :=
  RatOps.ofWords extractPrefix_computes
noncomputable def power_computes : PolyComputes (fun x=>BinaryRational.encode (power x)) :=
  RatOps.ofWords (discardPrefix_computes.comp extractPrefix_computes)
noncomputable def count_computes : PolyComputes count := discardPrefix_computes.comp discardPrefix_computes

noncomputable def step_computes (K : ℚ) : PolyComputes (step K) := by
  have hi := (const_computes [true]).append count_computes
  have hh := (RatOps.le threshold_computes power_computes).cond id_computes
    (extractPrefix_computes.pair ((RatOps.mul (RatOps.const K) power_computes).pair hi))
  unfold step
  simpa only [List.singleton_append,decide_eq_true_eq,id_eq] using hh
noncomputable def initial_computes : PolyComputes initial :=
  id_computes.pair ((const_computes (BinaryRational.encode 1)).pair (const_computes []))
noncomputable def iterated_computes (K : ℚ) (C : ℕ) : PolyComputes (iterated K C) :=
  ((fuel C).computes.pair ((cap K C).computes.pair initial_computes)).comp
    (BoundedIteration.run_computes (step_computes K))

noncomputable def run_computes (K : ℚ) (C : ℕ) : PolyComputes (run K C) := by
  have hh := (const_computes [true]).append ((iterated_computes K C).comp count_computes)
  unfold run
  simpa only [Function.comp_def,List.singleton_append] using hh

end MetricKMedianRecovery.BitMachine.BinaryPhaseFuel

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialAuto
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitialAuto
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
noncomputable def size_computes : PolyComputes size := (field_computes 1).append ((field_computes 2).comp Count.run_computes)
noncomputable def sizeRat : PolyComputes (fun x=>BinaryRational.encode ((size x).length:ℚ)) := BinaryInitial.unaryRat size_computes
noncomputable def low_computes : PolyComputes low := by
  change PolyComputes (fun x=>BinaryRational.encode (2/((size x).length:ℚ)^2))
  have hh := RatOps.div (RatOps.const 2) (RatOps.mul sizeRat sizeRat)
  simpa only [pow_two] using hh
noncomputable def threshold_computes : PolyComputes threshold := RatOps.add (RatOps.ofWords (field_computes 4))
  (RatOps.mul (RatOps.mul (RatOps.const 8) (BinaryInitial.unaryRat (field_computes 1))) (RatOps.ofWords (field_computes 4)))
noncomputable def total_computes (v : ℚ) (C : ℕ) : PolyComputes (total v C) := by
  change PolyComputes (fun x=>true::BinaryPhaseFuel.run (1+v^2) C (threshold x))
  simpa only [Function.comp_def,List.singleton_append] using
    (const_computes [true]).append (threshold_computes.comp (BinaryPhaseFuel.run_computes (1+v^2) C))
noncomputable def context_computes (v : ℚ) : PolyComputes (context v) := by
  unfold context
  simpa only [Function.comp_def,encode] using
    cons_computes (field_computes 0) (cons_computes (field_computes 1)
      (cons_computes ((field_computes 2).comp BinaryProjection.lift_computes) (cons_computes (const_computes [])
        (cons_computes ((field_computes 3).comp (map_computes BinaryProjection.originalWord_computes))
          (cons_computes (const_computes (BinaryRational.encode v)) (cons_computes (const_computes (BinaryRational.encode 0))
            (cons_computes (const_computes (BinaryRational.encode 0)) (const_computes []))))))))
noncomputable def initialInput_computes (v : ℚ) (C : ℕ) : PolyComputes (initialInput v C) :=
  cons_computes (context_computes v) (cons_computes size_computes (cons_computes size_computes
    (cons_computes (total_computes v C) (cons_computes (field_computes 5)
      (cons_computes low_computes (cons_computes (field_computes 4) (const_computes [])))))))
end MetricKMedianRecovery.BitMachine.BinaryInitialAuto

end OAI
end


