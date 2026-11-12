-- Prove2me | Definitions.Def_Q238L043
-- name    : Q238L043
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:45:31.420492+00:00
-- url     : https://prove2.me/theorems/3cfb6091-7450-4422-9ad4-317eaa25b625
-- title:
--   Definitions bundle Q238L043 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 135 declarations of OpenAI's Lean: 135 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.craw_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.cshape_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.csize_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.nword_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.rest_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryColorLabel.colorWord_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.context_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCorrection.applyWord_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCorrection.mapHistory_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCorrection.mapRow_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCorrection.mapSet_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.advance_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.finish_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.mapFree_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.mapPrefix_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.input_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.iterationInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.G_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.H_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.QG_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.Q_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.T_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.U_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.W`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.advanceInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.bankInput_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.banks_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.base`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.base_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.bf_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.c`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.contBase`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.contBase_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.crossInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.ctx_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.finishInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.key_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.mappedFree_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.mappedPrefix_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.power` and 95 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_BranchSeedLayout`, `KMedianRecovery_Branching_CompletionFair`, `KMedianRecovery_Encoding_ColorLabelMachine`, `KMedianRecovery_Encoding_CoupledEncode`, `KMedianRecovery_Encoding_HistoryBits`, `KMedianRecovery_Machines_CoupledPrimitives`, `KMedianRecovery_Machines_FiniteMachine`, `KMedianRecovery_Machines_InitialLoop`, `KMedianRecovery_Machines_LengthQuery`, `KMedianRecovery_Machines_LoopMachine`, `KMedianRecovery_Machines_LoopSize`, `KMedianRecovery_Machines_ResolveMachine`, `KMedianRecovery_Machines_ScanMachine`, `KMedianRecovery_Machines_SensitiveMachine`, `KMedianRecovery_Machines_StartResources`, `KMedianRecovery_Machines_StepMachine`, `KMedianRecovery_Recovery_Answer`, `KMedianRecovery_Recovery_CrossCount`, `KMedianRecovery_Recovery_FinishPhase`, `KMedianRecovery_Recovery_Fuel`, `KMedianRecovery_Recovery_PlanResult`, `KMedianRecovery_Strictness_BidBound`, `KMedianRecovery_Strictness_BidPoly`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L039` and `Q238L040` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L048`, `Q238L049`, `Q238L050` and `Q238L051`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.advanceInput_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.c_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.crossInput_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.finishInput_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.power_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryHistoryRun.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.count_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.history_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.counts_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.finishes_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.loopInput_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.chosen_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.count_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseCount.power_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.run_length_bound_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryResolve.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryScan.nodes_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinarySensitive.run_pack_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.advanceInput_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.c_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.crossInput_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.finishInput_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.power_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryHistoryRun.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.count_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.history_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.counts_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.finishes_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.loopInput_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.chosen_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.count_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseCount.power_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryResolve.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryScan.nodes_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinarySensitive.run_pack_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L039
import Definitions.Def_Q238L040

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
end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations BinaryArithmetic RationalLeaves
noncomputable def copied_computes : PolyComputes copied := by
  have hi : PolyComputes (fun x=>(value (extractPrefix x)+1).bits) := by
    simpa only [value_bits] using NatOps.add extractPrefix_computes (const_computes (1:ℕ).bits)
  have ht:=hi.pair ((discardPrefix_computes.comp parentWords_computes).pair (const_computes (BinaryRational.encode 0)))
  have hh := (NatOps.zero (discardPrefix_computes.comp levelWords_computes)).cond ht discardPrefix_computes
  unfold copied
  simpa only [Function.comp_def,decide_eq_true_eq] using hh
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
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionFair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionFair
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open Categorical.Explicit
variable {n q a p r c : ℕ}
noncomputable def context_computes : PolyComputes context :=
  cons_computes (extractPrefix_computes.comp (field_computes 10))
    (cons_computes (extractPrefix_computes.comp (field_computes 3))
      (cons_computes ((extractPrefix_computes.comp (field_computes 4)).comp Count.run_computes) (const_computes [])))
attribute [local irreducible] prepared
end MetricKMedianRecovery.BitMachine.BinaryCompletionFair

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
noncomputable def mapSet_computes : PolyComputes mapSet := mapRow_computes.comp BinaryLabel.sort_computes
end MetricKMedianRecovery.BitMachine.BinaryCorrection

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
noncomputable def mapFree_computes : PolyComputes mapFree := ((field_computes 2).pair (field_computes 0)).comp BinaryCorrection.mapSet_computes
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

namespace MetricKMedianRecovery.BitMachine.BinaryCross
open WordOperations WordList RationalLeaves BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)

noncomputable def cf_computes (n : ℕ) : PolyComputes (cf n) := extractPrefix_computes.comp (field_computes n)
noncomputable def opened_computes : PolyComputes opened :=
  ((cf_computes 1).pair (discardPrefix_computes.comp extractPrefix_computes)).comp BinaryFiniteContext.union_computes
noncomputable def finalOpened_computes : PolyComputes finalOpened :=
  (opened_computes.pair (discardPrefix_computes.comp discardPrefix_computes)).comp BinaryFiniteMachine.after_computes
end MetricKMedianRecovery.BitMachine.BinaryCross

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_PlanResult
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def copiedSet_computes : PolyComputes copiedSet := (mapWith_computes BinaryLabel.copied_computes).comp BinaryLabel.sort_computes
noncomputable def pool_computes : PolyComputes pool :=
  ((field_computes 1).pair (((field_computes 2).pair (field_computes 0)).comp copiedSet_computes)).comp union_computes
noncomputable def threeQ_computes : PolyComputes threeQ := by
  change PolyComputes (fun x=>(3*value (field 2 x)).bits)
  simpa only [value_bits] using NatOps.mul (const_computes (3:ℕ).bits) (field_computes 2)
noncomputable def threeQOne_computes : PolyComputes threeQOne := by
  change PolyComputes (fun x=>(value (threeQ x)+1).bits)
  simpa only [value_bits] using NatOps.add threeQ_computes (const_computes (1:ℕ).bits)
noncomputable def bankFirst_computes : PolyComputes bankFirst :=
  (cons_computes (field_computes 0) (cons_computes (field_computes 1) (cons_computes threeQ_computes (const_computes [])))).comp pool_computes
noncomputable def banks_computes : PolyComputes banks :=
  (cons_computes (field_computes 0) (cons_computes bankFirst_computes (cons_computes threeQOne_computes (const_computes [])))).comp pool_computes
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

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

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_StepMachine
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
noncomputable def bf_computes (i : ℕ) : PolyComputes (bf i) := (field_computes 0).comp (field_computes i)
noncomputable def mappedFree_computes : PolyComputes mappedFree :=
  (field_computes 6).comp (BinaryCoupled.mapFree_computes)
noncomputable def mappedPrefix_computes : PolyComputes mappedPrefix := by
  unfold mappedPrefix
  simpa only [Function.comp_def] using
    (field_computes 6).comp BinaryCoupled.mapPrefix_computes
noncomputable def Q_computes : PolyComputes Q :=
  ((const_computes []).pair mappedPrefix_computes).comp BinaryFiniteMachine.after_computes
noncomputable def power (x : List Bool) : List Bool := BinaryPhaseCount.power (pairBits (field 2 x,bf 5 x))
noncomputable def power_computes : PolyComputes power := by
  unfold power
  simpa only [Function.comp_def] using
    ((field_computes 2).pair (bf_computes 5)).comp BinaryPhaseCount.power_computes
noncomputable def base (x : List Bool) : List Bool := encode [bf 0 x,bf 1 x,bf 2 x,Q x,bf 4 x,bf 5 x,power x,sf 4 x]
noncomputable def base_computes : PolyComputes base :=
  list_computes [bf 0,bf 1,bf 2,Q,bf 4,bf 5,power,sf 4] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨bf_computes 0⟩
    · exact ⟨bf_computes 1⟩
    · exact ⟨bf_computes 2⟩
    · exact ⟨Q_computes⟩
    · exact ⟨bf_computes 4⟩
    · exact ⟨bf_computes 5⟩
    · exact ⟨power_computes⟩
    · exact ⟨sf_computes 4⟩
)
noncomputable def H_computes : PolyComputes H :=
  (sf_computes 5).comp (WordList.head_computes)
noncomputable def T_computes : PolyComputes T :=
  (sf_computes 5).comp (WordList.tail_computes)
noncomputable def G_computes : PolyComputes G :=
  (sf_computes 6).comp (WordList.head_computes)
noncomputable def U_computes : PolyComputes U :=
  (sf_computes 6).comp (WordList.tail_computes)
noncomputable def QG_computes : PolyComputes QG :=
  (Q_computes.pair G_computes).comp BinaryFiniteContext.union_computes
noncomputable def contBase (x : List Bool) : List Bool := encode [bf 0 x,bf 1 x,bf 2 x,QG x,bf 4 x,bf 5 x,power x,sf 4 x]
noncomputable def contBase_computes : PolyComputes contBase :=
  list_computes [bf 0,bf 1,bf 2,QG,bf 4,bf 5,power,sf 4] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨bf_computes 0⟩
    · exact ⟨bf_computes 1⟩
    · exact ⟨bf_computes 2⟩
    · exact ⟨QG_computes⟩
    · exact ⟨bf_computes 4⟩
    · exact ⟨bf_computes 5⟩
    · exact ⟨power_computes⟩
    · exact ⟨sf_computes 4⟩
)
noncomputable def W (x : List Bool) : List Bool := BinaryFiniteMachine.continuation (pairBits (field 1 x,pairBits (true::field 2 x,contBase x)))
noncomputable def ctx_computes : PolyComputes ctx :=
  list_computes [bf 2,Q,field 5] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨bf_computes 2⟩
    · exact ⟨Q_computes⟩
    · exact ⟨field_computes 5⟩
)
noncomputable def c (x : List Bool) : List Bool := BinaryCross.finalCount (pairBits (ctx x,pairBits (G x,W x)))
noncomputable def qbits_computes : PolyComputes qbits :=
  by
  change PolyComputes (fun x=>(field 2 x).length.bits)
  simpa only [Function.comp_def,UnaryResources.lengthBits_eq] using (field_computes 2).comp UnaryResources.lengthBits_computes
noncomputable def key_computes : PolyComputes key :=
  by
  change PolyComputes (fun x=>(3*value (qbits x)).bits)
  simpa only [value_bits] using NatOps.mul (const_computes (3:ℕ).bits) qbits_computes
noncomputable def crossInput (x : List Bool) : List Bool := encode [base x,key x,spare x,field 5 x,field 1 x,field 2 x,H x,G x,T x,W x]
noncomputable def bankInput_computes : PolyComputes bankInput :=
  list_computes [bf 2,mappedFree,qbits] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨bf_computes 2⟩
    · exact ⟨mappedFree_computes⟩
    · exact ⟨qbits_computes⟩
)
noncomputable def banks_computes : PolyComputes banks :=
  bankInput_computes.comp BinaryFiniteContext.banks_computes
noncomputable def prefixG_computes : PolyComputes prefixG :=
  mappedPrefix_computes.append (cons_computes G_computes (const_computes []))
noncomputable def finishInput (x : List Bool) : List Bool := encode [mappedFree x,sf 4 x,prefixG x,W x]
noncomputable def advanceInput (x : List Bool) : List Bool := encode [field 6 x,G x,W x,U x]
noncomputable def sandwiched (x : List Bool) : Bool := (decide (value (a x)<value (field 5 x)) && decide (value (field 5 x)<value (c x))) ||
  (decide (value (c x)<value (field 5 x)) && decide (value (field 5 x)<value (a x)))
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
attribute [local instance] RationalLeaves.metric
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
noncomputable def opened (x : List Bool) : List Bool := BinaryFiniteMachine.after (pairBits ([],history x))
noncomputable def count (x : List Bool) : List Bool := BinaryFiniteContext.countInter (pairBits (opened x,bf 2 x))
end MetricKMedianRecovery.BitMachine.BinaryInitialQuery

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
attribute [local irreducible] BinaryInitialQuery.count BinaryInitialQuery.history BinaryBisection.run
noncomputable def ctx_computes : PolyComputes ctx := (field_computes 3).pair (field_computes 0)

noncomputable def loInput_computes : PolyComputes loInput := ctx_computes.pair (field_computes 5)

noncomputable def loCount (x : List Bool) : List Bool := BinaryInitialQuery.count (loInput x)

noncomputable def loHistory (x : List Bool) : List Bool := BinaryInitialQuery.history (loInput x)

noncomputable def loFinish (x : List Bool) : List Bool := encode [((fun _=>[])) x,(field 5) x,(loHistory) x]

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

end MetricKMedianRecovery.BitMachine.BinaryInitial

end OAI
end


