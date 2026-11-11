-- Prove2me | Definitions.Def_Q238K043
-- name    : Q238K043
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:43:44.89892+00:00
-- url     : https://prove2.me/theorems/8f563439-3cad-4bd5-a198-e8ebe6ede992
-- title:
--   Definitions bundle Q238K043 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 136 declarations of OpenAI's Lean: 136 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.craw_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.cshape_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.csize_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.nword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.rest_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.postInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryColorLabel.colorWord_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCorrection.applyWord_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCorrection.mapHistory_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCorrection.mapRow_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.advance_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.finish_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.mapPrefix_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.input_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.iterationInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.next`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.stateRun`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.step`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.G_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.U_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.W`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.active`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.advanceInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.base`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.c`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.contBase`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.crossInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.finishInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.power`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.resolveInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.sandwiched`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.sf_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.containsItem_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.inter_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.scanInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.after_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.continuation` and 96 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_BranchSeedLayout`, `KMedianRecovery_Encoding_ColorLabelMachine`, `KMedianRecovery_Encoding_CoupledEncode`, `KMedianRecovery_Encoding_HistoryBits`, `KMedianRecovery_Encoding_LabelLookup`, `KMedianRecovery_Machines_CoupledPrimitives`, `KMedianRecovery_Machines_FiniteMachine`, `KMedianRecovery_Machines_InitialLoop`, `KMedianRecovery_Machines_LengthQuery`, `KMedianRecovery_Machines_LoopMachine`, `KMedianRecovery_Machines_LoopSize`, `KMedianRecovery_Machines_MatchFold`, `KMedianRecovery_Machines_MatchSize`, `KMedianRecovery_Machines_ResolveMachine`, `KMedianRecovery_Machines_ScanMachine`, `KMedianRecovery_Machines_SensitiveMachine`, `KMedianRecovery_Machines_StartResources`, `KMedianRecovery_Machines_StepMachine`, `KMedianRecovery_Recovery_Answer`, `KMedianRecovery_Recovery_CrossCount`, `KMedianRecovery_Recovery_FinishPhase`, `KMedianRecovery_Recovery_Fuel`, `KMedianRecovery_Recovery_InitialAuto`, `KMedianRecovery_Recovery_InitialProject`, `KMedianRecovery_Recovery_RegularChain`, `KMedianRecovery_Strictness_BidBound`, `KMedianRecovery_Strictness_BidPoly`, `KMedianRecovery_Strictness_SurplusPostprocess`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K039` and `Q238K040` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K048`, `Q238K049` and `Q238K050`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.run_initial_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.advanceInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.c_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.crossInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.finishInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.power_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryHistoryRun.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.count_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.history_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.counts_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.finishes_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.loopInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.chosen_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.count_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.step_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseCount.power_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.run_length_bound_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRegularChain.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRegular.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryResolve.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryScan.nodes_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinarySensitive.run_pack_s238`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.run_initial_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.advanceInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.c_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.crossInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.finishInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.power_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryHistoryRun.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.count_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.history_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.counts_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.finishes_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.loopInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.chosen_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.count_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.step_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseCount.power_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRegularChain.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRegular.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryResolve.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryScan.nodes_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinarySensitive.run_pack_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K039
import Definitions.Def_Q238K040

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Answer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFinish
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
noncomputable def step_computes : PolyComputes step := by
  have h := (answer_computes.comp isEmpty_computes).cond id_computes
    ((id_computes.pair (answer_computes.comp WordOperations.tail_computes)).comp BinaryPhaseUpdate.run_computes)
  change PolyComputes (fun x=>if answer x=[] then x else BinaryPhaseUpdate.run (pairBits (x,(answer x).tail)))
  simpa only [Function.comp_def,decide_eq_true_eq,id_eq] using h
end MetricKMedianRecovery.BitMachine.BinaryPhaseFinish

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_BidPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFinish
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate

noncomputable def cap : PolynomialCounter capPoly := PolynomialCounter.choose capPoly

noncomputable def run (x : List Bool) : List Bool :=
  BoundedIteration.run step (pairBits (extractPrefix x,pairBits (cap.word (discardPrefix x),discardPrefix x)))
noncomputable def run_computes : PolyComputes run :=
  (extractPrefix_computes.pair ((discardPrefix_computes.comp cap.computes).pair discardPrefix_computes)).comp
    (BoundedIteration.run_computes step_computes)
end MetricKMedianRecovery.BitMachine.BinaryPhaseFinish

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Fuel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseRun
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
noncomputable def completed (x : List Bool) : List Bool := BinaryPhaseFinish.run (pairBits (fuel x,x))
noncomputable def completed_computes : PolyComputes completed := (fuel_computes.pair id_computes).comp BinaryPhaseFinish.run_computes
noncomputable def step : List Bool → List Bool := BinaryPhaseAdvance.run ∘ completed
noncomputable def step_computes : PolyComputes step := completed_computes.comp BinaryPhaseAdvance.run_computes
end MetricKMedianRecovery.BitMachine.BinaryPhaseRun

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_BidBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseRun
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate RationalHeight
open BinaryPhaseFinish
noncomputable def bidBound : Polynomial ℕ := BinaryPhaseFinish.bidPoly.comp (100*(Polynomial.X+1)^2)
noncomputable def sizeBound : Polynomial ℕ := 1000*(Polynomial.X+1)^3+4*(Polynomial.X+1)*bidBound
noncomputable def cap : PolynomialCounter sizeBound := PolynomialCounter.choose sizeBound
noncomputable def run (x : List Bool) : List Bool := BoundedIteration.run step
  (pairBits (extractPrefix x,pairBits (cap.word x,discardPrefix x)))
noncomputable def run_computes : PolyComputes run :=
  (extractPrefix_computes.pair (cap.computes.pair discardPrefix_computes)).comp
    (BoundedIteration.run_computes step_computes)
end MetricKMedianRecovery.BitMachine.BinaryPhaseRun

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_HistoryBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryHistoryRun
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
open BinaryRunTrace (finished finished_computes )
attribute [local irreducible] finished finished_computes
attribute [local irreducible] chunk chunk_computes
noncomputable def step (x : List Bool) : List Bool :=
  pairBits (BinaryPhaseRun.step (extractPrefix x),discardPrefix x++chunk (extractPrefix x))
noncomputable def step_computes : PolyComputes step :=
  (extractPrefix_computes.comp BinaryPhaseRun.step_computes).pair
    (discardPrefix_computes.append (extractPrefix_computes.comp chunk_computes))
noncomputable def capPoly : Polynomial ℕ :=
  2*BinaryPhaseRun.sizeBound+1+Polynomial.X*(chunk_computes.lengthPolynomial.comp BinaryPhaseRun.sizeBound)
noncomputable def cap : PolynomialCounter capPoly := PolynomialCounter.choose capPoly
noncomputable def run (x : List Bool) : List Bool :=
  BoundedIteration.run step (pairBits (extractPrefix x,pairBits (cap.word x,pairBits (discardPrefix x,[]))))
noncomputable def run_computes : PolyComputes run :=
  (extractPrefix_computes.pair (cap.computes.pair (discardPrefix_computes.pair (const_computes [])))).comp
    (BoundedIteration.run_computes step_computes)
end MetricKMedianRecovery.BitMachine.BinaryHistoryRun

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabelLookup
open WordOperations WordList RationalLeaves
noncomputable def history_computes : PolyComputes history := mapWith_computes run_computes
end MetricKMedianRecovery.BitMachine.BinaryLabelLookup

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FinishPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseCount
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate BinaryOpeningPayment
attribute [local irreducible] WordList.map WordList.Indices.run WordList.Lookup.run
  WordList.Fold.run BinaryPhaseRun.run
noncomputable def power (x : List Bool) : List Bool := BinaryPhaseAdvance.sf 3
  (BinaryPhaseRun.run (pairBits (extractPrefix x,powerInput (discardPrefix x))))
noncomputable def power_computes : PolyComputes power :=
  ((extractPrefix_computes.pair (discardPrefix_computes.comp powerInput_computes)).comp BinaryPhaseRun.run_computes).comp
    (BinaryPhaseAdvance.sf_computes 3)
end MetricKMedianRecovery.BitMachine.BinaryPhaseCount

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_FiniteMachine
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteMachine
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (pack labels)

noncomputable def data_computes : PolyComputes data := discardPrefix_computes.comp discardPrefix_computes
noncomputable def phase (x : List Bool) : List Bool :=
  BinaryPhaseCount.power (pairBits (extractPrefix (discardPrefix x),field 5 (data x)))
noncomputable def phase_computes : PolyComputes phase := by
  have phaseComputes :=
    ((discardPrefix_computes.comp extractPrefix_computes).pair (data_computes.comp (field_computes 5))).comp
      BinaryPhaseCount.power_computes
  unfold phase
  simpa only [Function.comp_def] using phaseComputes
noncomputable def start (x : List Bool) : List Bool := BinaryPhaseCount.start
  (pairBits (BinaryFiniteContext.run (data x),phase x))
noncomputable def start_computes : PolyComputes start :=
  ((data_computes.comp BinaryFiniteContext.run_computes).pair phase_computes).comp BinaryPhaseCount.start_computes
noncomputable def history (x : List Bool) : List Bool :=
  discardPrefix (BinaryHistoryRun.run (pairBits (extractPrefix x,start x)))
noncomputable def history_computes : PolyComputes history :=
  ((extractPrefix_computes.pair start_computes).comp BinaryHistoryRun.run_computes).comp discardPrefix_computes
noncomputable def continuation (x : List Bool) : List Bool := BinaryLabelLookup.history
  (pairBits (BinaryFiniteContext.alphabet (data x),history x))
noncomputable def continuation_computes : PolyComputes continuation := by
  have continuationComputes :=
    ((data_computes.comp BinaryFiniteContext.alphabet_computes).pair history_computes).comp
      BinaryLabelLookup.history_computes
  unfold continuation
  simpa only [Function.comp_def] using continuationComputes
end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations BinaryArithmetic RationalLeaves
noncomputable def swapped_computes : PolyComputes swapped :=
  ((discardPrefix_computes.pair (extractPrefix_computes.comp extractPrefix_computes)).comp eq_computes).cond
    (extractPrefix_computes.comp discardPrefix_computes)
    (((discardPrefix_computes.pair (extractPrefix_computes.comp discardPrefix_computes)).comp eq_computes).cond
      (extractPrefix_computes.comp extractPrefix_computes) discardPrefix_computes)
end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteMachine
open WordOperations WordList RationalLeaves PhaseSequence
open BinaryFiniteContext (labels setBits)
noncomputable def after_computes : PolyComputes after :=
  (extractPrefix_computes.append (discardPrefix_computes.comp Flatten.run_computes)).comp BinaryLabel.sort_computes
end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_ColorLabelMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryColorLabel
open WordOperations WordList BinaryArithmetic
attribute [local irreducible] WordList.mapWith
noncomputable def colorWord_computes : PolyComputes colorWord := by
  unfold colorWord
  simpa only [decide_eq_true_eq,id_eq,value_bits] using
    (NatOps.lt id_computes (const_computes (2:ℕ).bits)).cond (const_computes (0:ℕ).bits)
      ((NatOps.eq id_computes (const_computes (2:ℕ).bits)).cond (const_computes (1:ℕ).bits) (const_computes (2:ℕ).bits))
end MetricKMedianRecovery.BitMachine.BinaryColorLabel

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchSeedLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchRandomize
open WordOperations WordList BinaryArithmetic BinaryBranchContext
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] Count.run BinaryBisection.logWord RawTake.run RawDrop.run BinaryColorLabel.colors BinaryColorLabel.labels
noncomputable def nword_computes : PolyComputes nword := (field_computes 0).comp Count.run_computes
noncomputable def cshape_computes : PolyComputes cshape := cons_computes nword_computes (cons_computes (const_computes _) (const_computes []))
noncomputable def csize_computes : PolyComputes csize := by
  unfold csize
  simpa only [value_bits,Function.comp_def] using NatOps.mul (nword_computes.comp UnaryResources.lengthBits_computes) (const_computes (2:ℕ).bits)
noncomputable def craw_computes : PolyComputes craw :=
  ((extractPrefix_computes.comp csize_computes).pair discardPrefix_computes).comp RawTake.run_computes
noncomputable def rest_computes : PolyComputes rest :=
  ((extractPrefix_computes.comp csize_computes).pair discardPrefix_computes).comp RawDrop.run_computes
end MetricKMedianRecovery.BitMachine.BinaryBranchRandomize

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_CoupledEncode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCorrection
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
noncomputable def applyWord_computes : PolyComputes applyWord :=
  by
  change PolyComputes (fun x=>if extractPrefix x=[] then discardPrefix x else BinaryLabel.swapped x)
  simpa only [Function.comp_def,decide_eq_true_eq] using
    (extractPrefix_computes.comp isEmpty_computes).cond discardPrefix_computes BinaryLabel.swapped_computes
noncomputable def mapRow_computes : PolyComputes mapRow := mapWith_computes applyWord_computes
noncomputable def mapHistory_computes : PolyComputes mapHistory := mapWith_computes mapRow_computes
end MetricKMedianRecovery.BitMachine.BinaryCorrection

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
attribute [local irreducible] BinaryCorrection.mapHistory
noncomputable def mapPrefix_computes : PolyComputes mapPrefix := by
  unfold mapPrefix
  exact ((field_computes 2).pair (field_computes 1)).comp BinaryCorrection.mapHistory_computes
noncomputable def finish_computes : PolyComputes finish := cons_computes (field_computes 0)
  (cons_computes (field_computes 1) (cons_computes ((field_computes 2).append (field_computes 3)) (const_computes [])))
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CoupledPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
noncomputable def advance_computes : PolyComputes advance :=
  list_computes [field 0 ∘ field 0,(fun x=>field 1 (field 0 x)++cons (field 1 x) []),field 2 ∘ field 0,
    field 3 ∘ field 0,field 4 ∘ field 0,field 2,field 3] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨(field_computes 0).comp (field_computes 0)⟩
    · exact ⟨((field_computes 0).comp (field_computes 1)).append (cons_computes (field_computes 1) (const_computes []))⟩
    · exact ⟨(field_computes 0).comp (field_computes 2)⟩
    · exact ⟨(field_computes 0).comp (field_computes 3)⟩
    · exact ⟨(field_computes 0).comp (field_computes 4)⟩
    · exact ⟨field_computes _⟩
    · exact ⟨field_computes _⟩)
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CrossCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList RationalLeaves BinaryArithmetic
noncomputable def containsItem_computes : PolyComputes (fun x=>[containsItem x]) :=
  (discardPrefix_computes.pair extractPrefix_computes).comp BinaryLabel.contains_computes
noncomputable def inter_computes : PolyComputes inter :=
  ((discardPrefix_computes.pair extractPrefix_computes).comp (filterWith_computes containsItem_computes)).comp BinaryLabel.sort_computes
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LengthQuery
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
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
attribute [local irreducible] BinaryFiniteMachine.continuation

noncomputable def interior (x : List Bool) : List Bool := BinaryFiniteMachine.continuation
  (pairBits (cf 1 x,pairBits (cf 2 x,base x)))
noncomputable def chosen (x : List Bool) : List Bool := if isZero x then cf 6 x else if isUpper x then cf 7 x else interior x
noncomputable def finalOpened (x : List Bool) : List Bool := BinaryFiniteMachine.after (pairBits (opened x,chosen x))
noncomputable def count (x : List Bool) : List Bool := BinaryFiniteContext.countInter (pairBits (finalOpened x,field 2 (cf 0 x)))
end MetricKMedianRecovery.BitMachine.BinaryLengthQuery

namespace MetricKMedianRecovery.BitMachine.BinaryLengthSearch
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def leftHistory : List Bool→List Bool := BinaryLengthQuery.chosen ∘ leftInput
noncomputable def rightHistory : List Bool→List Bool := BinaryLengthQuery.chosen ∘ rightInput
noncomputable def leftSuccess (x : List Bool) : List Bool := encode [(0:ℕ).bits,lower x,[],leftHistory x,[]]
noncomputable def rightSuccess (x : List Bool) : List Bool := encode [(0:ℕ).bits,upper x,[],rightHistory x,[]]
noncomputable def bracket (x : List Bool) : List Bool := encode [(1:ℕ).bits,lower x,upper x,leftHistory x,rightHistory x]
noncomputable def leftEqual (x : List Bool) : Bool := decide (value (BinaryLengthQuery.count (leftInput x))=value (boundK x))
noncomputable def rightEqual (x : List Bool) : Bool := decide (value (BinaryLengthQuery.count (rightInput x))=value (boundK x))
noncomputable def finish (x : List Bool) : List Bool :=
  if leftEqual x then leftSuccess x else if rightEqual x then rightSuccess x else bracket x
noncomputable def input (x : List Bool) : List Bool := pairBits (x,BinaryOrientedSearch.run BinaryLengthQuery.count x)
noncomputable def run : List Bool→List Bool := finish ∘ input
end MetricKMedianRecovery.BitMachine.BinaryLengthSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SensitiveMachine
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
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
noncomputable def earlyEqual (x : List Bool) : Bool := decide (value (BinaryLengthQuery.count (atZero x))=value (field 5 x))
noncomputable def run (x : List Bool) : List Bool := if earlyEqual x then early x else BinaryLengthSearch.run (searchInput x)
end MetricKMedianRecovery.BitMachine.BinarySensitive

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ResolveMachine
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryResolve
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge CanonicalLengthView
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
noncomputable def planResultInput (x : List Bool) : List Bool := encode [sensitiveInput x,field 7 x,field 8 x,BinarySensitive.run (sensitiveInput x)]
noncomputable def sensitive (x : List Bool) : List Bool := if view x=[] then
  pairBits ([],BinaryCoupled.finish (fallbackInput x)) else BinaryPlanResult.run (planResultInput x)
noncomputable def run (x : List Bool) : List Bool := if value (rf 0 x)=0 then
  pairBits ([],BinaryCoupled.finish (finishInput x)) else if value (rf 0 x)=1 then
  pairBits ([true],BinaryCoupled.same (sameInput x)) else sensitive x
end MetricKMedianRecovery.BitMachine.BinaryResolve

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MatchFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMatch
open WordOperations WordList RationalLeaves CanonicalMatch
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)

attribute [local irreducible] BinaryLabel.copied
noncomputable def advanced : List Bool → List Bool := BinaryAdvance.run ∘ advancingInput
attribute [local irreducible] advanced
noncomputable def rest : List Bool → List Bool := field 0 ∘ advanced
noncomputable def vertices (x : List Bool) : List Bool := sf 2 x++field 1 (advanced x)
noncomputable def step (x : List Bool) : List Bool := encode [front x,rest x,vertices x]
end MetricKMedianRecovery.BitMachine.BinaryMatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MatchSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMatch
open WordOperations WordList RationalLeaves CanonicalMatch CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

noncomputable def run (x : List Bool) : List Bool := CappedFold.run step (pairBits (capacity.word x,x))
end MetricKMedianRecovery.BitMachine.BinaryMatch

namespace MetricKMedianRecovery.BitMachine.BinaryRegular
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)

noncomputable def matched : List Bool → List Bool := BinaryMatch.run ∘ matchInput
noncomputable def prunedInput (x : List Bool) : List Bool := pairBits (field 2 x,field 1 (matched x))
noncomputable def run (x : List Bool) : List Bool := field 2 (matched x)++BinarySuffix.prune (prunedInput x)
end MetricKMedianRecovery.BitMachine.BinaryRegular

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RegularChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRegularChain
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryRegular.run BinaryRefine.run
noncomputable def vertices (x : List Bool) : List Bool := cons (field 4 x) (BinaryRegular.run (regularInput x))
noncomputable def run (x : List Bool) : List Bool := BinaryRefine.run (pairBits (context x,vertices x))
end MetricKMedianRecovery.BitMachine.BinaryRegularChain

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ScanMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryScan
open WordOperations WordList RationalLeaves CanonicalMergeCrossing
open BinaryCross (ctxBits nodeBits resultBits)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryFiniteMachine.continuation BinaryNodeScan.run
noncomputable def node (x : List Bool) : List Bool := pairBits (discardPrefix x,BinaryFiniteMachine.continuation (contInput x))
noncomputable def nodes (x : List Bool) : List Bool :=
  cons (field 5 x) (mapWith node (pairBits (mapCtx x,field 6 x)))
noncomputable def scanInput (x : List Bool) : List Bool := encode [field 3 x,field 4 x,nodes x]
noncomputable def run : List Bool → List Bool := BinaryNodeScan.run ∘ scanInput
end MetricKMedianRecovery.BitMachine.BinaryScan

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteCross
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryRegularChain.run BinaryScan.run
noncomputable def scanInput (x : List Bool) : List Bool :=
  encode [field 0 x,field 4 x,nextQ x,crossCtx x,field 9 x,firstNode x,BinaryRegularChain.run (chainInput x)]
noncomputable def run : List Bool → List Bool := BinaryScan.run ∘ scanInput
end MetricKMedianRecovery.BitMachine.BinaryFiniteCross

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_StepMachine
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledStep
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge PhaseHistoryTransfer
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outcomeBits)
noncomputable def sf_computes (i : ℕ) : PolyComputes (sf i) := (field_computes 6).comp (field_computes i)
noncomputable def power (x : List Bool) : List Bool := BinaryPhaseCount.power (pairBits (field 2 x,bf 5 x))
noncomputable def base (x : List Bool) : List Bool := encode [bf 0 x,bf 1 x,bf 2 x,Q x,bf 4 x,bf 5 x,power x,sf 4 x]
noncomputable def G_computes : PolyComputes G :=
  (sf_computes 6).comp (WordList.head_computes)
noncomputable def U_computes : PolyComputes U :=
  (sf_computes 6).comp (WordList.tail_computes)
noncomputable def contBase (x : List Bool) : List Bool := encode [bf 0 x,bf 1 x,bf 2 x,QG x,bf 4 x,bf 5 x,power x,sf 4 x]
noncomputable def W (x : List Bool) : List Bool := BinaryFiniteMachine.continuation (pairBits (field 1 x,pairBits (true::field 2 x,contBase x)))
noncomputable def c (x : List Bool) : List Bool := BinaryCross.finalCount (pairBits (ctx x,pairBits (G x,W x)))
noncomputable def crossInput (x : List Bool) : List Bool := encode [base x,key x,spare x,field 5 x,field 1 x,field 2 x,H x,G x,T x,W x]
noncomputable def resolveInput (x : List Bool) : List Bool := encode [base x,field 1 x,field 2 x,leafKey x,field 3 x,field 5 x,field 4 x,banks x,mappedPrefix x,(BinaryFiniteCross.run ∘ crossInput) x]
noncomputable def finishInput (x : List Bool) : List Bool := encode [mappedFree x,sf 4 x,prefixG x,W x]
noncomputable def advanceInput (x : List Bool) : List Bool := encode [field 6 x,G x,W x,U x]
noncomputable def sandwiched (x : List Bool) : Bool := (decide (value (a x)<value (field 5 x)) && decide (value (field 5 x)<value (c x))) ||
  (decide (value (c x)<value (field 5 x)) && decide (value (field 5 x)<value (a x)))
noncomputable def active (x : List Bool) : List Bool := if decide (value (c x)=value (field 5 x)) then pairBits ([],BinaryCoupled.finish (finishInput x))
  else if sandwiched x then BinaryResolve.run (resolveInput x) else pairBits ([true],BinaryCoupled.advance (advanceInput x))
noncomputable def run (x : List Bool) : List Bool := if nonempty x then active x else pairBits ([],BinaryCoupled.finish (fallbackInput x))
end MetricKMedianRecovery.BitMachine.BinaryCoupledStep

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledLoop
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryCoupled (stateBits outcomeBits outputBits)
noncomputable def input_computes : PolyComputes input := list_computes
  [field 0,List.tail ∘ field 1,field 2,field 3,field 4,field 5,discardPrefix ∘ field 6] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨field_computes _⟩ | exact ⟨(field_computes _).comp WordOperations.tail_computes⟩ |
      exact ⟨(field_computes _).comp discardPrefix_computes⟩)
noncomputable def next (x : List Bool) : List Bool := encode [field 0 x,(field 1 x).tail,true::field 2 x,
  field 3 x,field 4 x,field 5 x,BinaryCoupledStep.run (input x)]
noncomputable def step (x : List Bool) : List Bool :=
  if extractPrefix (field 6 x)=[] then x else if field 1 x=[] then x else next x
attribute [local instance] RationalLeaves.metric
end MetricKMedianRecovery.BitMachine.BinaryCoupledLoop

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledLoop
open WordOperations WordList BinaryArithmetic RationalLeaves RationalHeight CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryCoupled (stateBits outcomeBits outputBits)
noncomputable def iterationInput_computes : PolyComputes iterationInput :=
  (field_computes 1).pair (capacity.computes.pair id_computes)
noncomputable def stateRun : List Bool→List Bool := BoundedIteration.run step ∘ iterationInput
noncomputable def run : List Bool→List Bool := discardPrefix ∘ field 6 ∘ stateRun
attribute [local instance] RationalLeaves.metric
attribute [local irreducible] BinaryCoupledStep.run
end MetricKMedianRecovery.BitMachine.BinaryCoupledLoop

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_StartResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitialQuery
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
attribute [local irreducible] BinaryFiniteMachine.continuation

noncomputable def bf_computes (j : ℕ) : PolyComputes (bf j) :=
  (extractPrefix_computes.comp discardPrefix_computes).comp (field_computes j)
noncomputable def atPrice_computes : PolyComputes atPrice :=
  list_computes [bf 0,bf 1,bf 2,bf 3,bf 4,bf 5,bf 6,discardPrefix] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨bf_computes _⟩ | exact ⟨discardPrefix_computes⟩)
noncomputable def history (x : List Bool) : List Bool := BinaryFiniteMachine.continuation
  (pairBits (extractPrefix (extractPrefix x),pairBits ([],atPrice x)))
noncomputable def history_computes : PolyComputes history :=
  ((extractPrefix_computes.comp extractPrefix_computes).pair ((const_computes []).pair atPrice_computes)).comp
    BinaryFiniteMachine.continuation_computes
noncomputable def opened (x : List Bool) : List Bool := BinaryFiniteMachine.after (pairBits ([],history x))
noncomputable def opened_computes : PolyComputes opened :=
  ((const_computes []).pair history_computes).comp BinaryFiniteMachine.after_computes
noncomputable def count (x : List Bool) : List Bool := BinaryFiniteContext.countInter (pairBits (opened x,bf 2 x))
end MetricKMedianRecovery.BitMachine.BinaryInitialQuery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_InitialLoop
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
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
attribute [local irreducible] BinaryInitialQuery.count BinaryInitialQuery.history BinaryCoupledLoop.run BinaryBisection.run
noncomputable def ctx_computes : PolyComputes ctx := (field_computes 3).pair (field_computes 0)

noncomputable def loInput_computes : PolyComputes loInput := ctx_computes.pair (field_computes 5)

noncomputable def loCount (x : List Bool) : List Bool := BinaryInitialQuery.count (loInput x)

noncomputable def loHistory (x : List Bool) : List Bool := BinaryInitialQuery.history (loInput x)
noncomputable def loHistory_computes : PolyComputes loHistory := loInput_computes.comp BinaryInitialQuery.history_computes

noncomputable def loFinish (x : List Bool) : List Bool := encode [((fun _=>[])) x,(field 5) x,(loHistory) x]
noncomputable def loFinish_computes : PolyComputes loFinish := list_computes [(fun _=>[]),field 5,loHistory] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨const_computes []⟩
  · exact ⟨field_computes 5⟩
  · exact ⟨loHistory_computes⟩)

noncomputable def bracket (x : List Bool) : List Bool := BinaryBisection.run BinaryInitialQuery.count (bracketInput x)

noncomputable def lower (x : List Bool) : List Bool := extractPrefix (bracket x)

noncomputable def lowerInput (x : List Bool) : List Bool := pairBits (ctx x,lower x)

noncomputable def lowerCount (x : List Bool) : List Bool := BinaryInitialQuery.count (lowerInput x)

noncomputable def lowerHistory (x : List Bool) : List Bool := BinaryInitialQuery.history (lowerInput x)

noncomputable def lowerFinish (x : List Bool) : List Bool := encode [((fun _=>[])) x,(lower) x,(lowerHistory) x]

noncomputable def upper (x : List Bool) : List Bool := discardPrefix (bracket x)

noncomputable def upperInput (x : List Bool) : List Bool := pairBits (ctx x,upper x)

noncomputable def upperCount (x : List Bool) : List Bool := BinaryInitialQuery.count (upperInput x)

noncomputable def upperHistory (x : List Bool) : List Bool := BinaryInitialQuery.history (upperInput x)

noncomputable def upperFinish (x : List Bool) : List Bool := encode [((fun _=>[])) x,(upper) x,(upperHistory) x]

noncomputable def initialState (x : List Bool) : List Bool := encode [((fun _=>[])) x,((fun _=>[])) x,((fun _=>[])) x,(lower) x,(upper) x,(upperHistory) x,(lowerHistory) x]

noncomputable def initialOutcome (x : List Bool) : List Bool := pairBits ([true],initialState x)

noncomputable def loopInput (x : List Bool) : List Bool := encode [(field 0) x,(field 3) x,((fun _=>[])) x,(far) x,(field 2) x,(field 4) x,(initialOutcome) x]

noncomputable def normal (x : List Bool) : List Bool := if value (lowerCount x)=value (field 4 x) then lowerFinish x else
  if value (upperCount x)=value (field 4 x) then upperFinish x else BinaryCoupledLoop.run (loopInput x)

noncomputable def run (x : List Bool) : List Bool := if value (loCount x)≤value (field 4 x) then pairBits ([],loFinish x) else pairBits ([true],normal x)

end MetricKMedianRecovery.BitMachine.BinaryInitial

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
noncomputable def run (v : ℚ) (C : ℕ) : List Bool→List Bool := BinaryInitial.run ∘ initialInput v C
end MetricKMedianRecovery.BitMachine.BinaryInitialAuto

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialProject
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitialProject
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
attribute [local irreducible] BinaryProjection.run BinaryFiniteMachine.after
noncomputable def run (v : ℚ) (C : ℕ) : List Bool→List Bool := extract ∘ BinaryInitialAuto.run v C
end MetricKMedianRecovery.BitMachine.BinaryInitialProject

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_SurplusPostprocess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
variable {m : ℕ}
noncomputable def postInput (v : ℚ) (C : ℕ) (x : List Bool) : List Bool :=
  encode [field 0 (extractPrefix x),field 1 (extractPrefix x),field 2 (extractPrefix x),
    BinaryInitialProject.run v C (extractPrefix x),discardPrefix x]
end MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus

end OAI
end


