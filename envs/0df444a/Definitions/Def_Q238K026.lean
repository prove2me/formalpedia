-- Prove2me | Definitions.Def_Q238K026
-- name    : Q238K026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:20:30.01453+00:00
-- url     : https://prove2.me/theorems/0cb91756-4b70-4bae-99c9-39a4cc7ce9b4
-- title:
--   Definitions bundle Q238K026 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 120 declarations of OpenAI's Lean: 118 definitions and 2 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.bagWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFill.options`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFill.pick`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFill.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCorrection.encode`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCorrection.mapSet`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.leafBank`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.leafResult`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.mapFree`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.outcomeBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.stateBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledState.encode`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.Q`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.QG`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.bankInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.banks`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.ctx`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.mappedFree`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.finalOpened`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.opened`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix.twice_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.bankFirst`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.banks`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.copiedSet`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.inter`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pool`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.after`, `OAI.MetricKMedianRecovery.BitMachine.BinaryHistoryRun.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.context`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.count`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.layout`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.output`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.candidates`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.optionOutput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.result` and 78 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_IntegralRecoveryDemand`, `KMedianRecovery_Algorithms_IntegralRecoveryRepeat`, `KMedianRecovery_Algorithms_IntegralRecoverySemantics`, `KMedianRecovery_Algorithms_IntegralRecoverySuccess`, `KMedianRecovery_Branching_BranchTapeBound`, `KMedianRecovery_Branching_CategoricalChoice`, `KMedianRecovery_Branching_CategoricalRawPrep`, `KMedianRecovery_Branching_ObservableCapacity`, `KMedianRecovery_Branching_RandomizedZeroBranch`, `KMedianRecovery_Encoding_CoupledEncode`, `KMedianRecovery_Encoding_DuplicateMatrix`, `KMedianRecovery_Encoding_HistoryBits`, `KMedianRecovery_Encoding_LengthEncode`, `KMedianRecovery_Encoding_RationalLeaves`, `KMedianRecovery_Encoding_StateBits`, `KMedianRecovery_Encoding_StateBits2`, `KMedianRecovery_Encoding_WordExtras`, `KMedianRecovery_Geometry_LocalBest`, `KMedianRecovery_Geometry_LocalCandidates`, `KMedianRecovery_Geometry_LocalFuel`, `KMedianRecovery_Geometry_LocalRefineMachine`, `KMedianRecovery_Geometry_LocalSets`, `KMedianRecovery_Geometry_MetricCost2`, `KMedianRecovery_Machines_CoupledPrimitives`, `KMedianRecovery_Machines_FiniteMachine`, `KMedianRecovery_Machines_InitialLoop`, `KMedianRecovery_Machines_LengthQuery`, `KMedianRecovery_Machines_LoopMachine`, `KMedianRecovery_Machines_MatchFold`, `KMedianRecovery_Machines_MatchSize`, `KMedianRecovery_Machines_ProjectionMachine`, `KMedianRecovery_Machines_RecoveryTape`, `KMedianRecovery_Machines_ScanMachine`, `KMedianRecovery_Machines_SensitiveMachine`, `KMedianRecovery_Machines_StepMachine`, `KMedianRecovery_Recovery_Basic`, `KMedianRecovery_Recovery_CrossCount`, `KMedianRecovery_Recovery_FiniteContext`, `KMedianRecovery_Recovery_InitialAuto`, `KMedianRecovery_Recovery_LeafOrder`, `KMedianRecovery_Recovery_ListSetExtra`, `KMedianRecovery_Recovery_Min`, `KMedianRecovery_Recovery_Pack11`, `KMedianRecovery_Recovery_PlanResult`, `KMedianRecovery_Recovery_RecoveryCandidates`, `KMedianRecovery_Recovery_RefineMath`, `KMedianRecovery_Recovery_RowInput`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K017`, `Q238K018`, `Q238K019`, `Q238K020` and `Q238K021` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K029`, `Q238K030` and `Q238K031`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.bagWords_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.Q_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.mapped_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.alphabet_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.selected_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.context_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output_success_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.amplified_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.anchorInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricBest.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningNearest.run_source_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.bids_context_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseFirst_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate.updatedBudget_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryRawOpening_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.result_success_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.fair_zero_completion_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.successful_completion_s238`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.bagWords_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.Q_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.mapped_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.alphabet_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.selected_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.context_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output_success_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.amplified_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.anchorInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricBest.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.coefficient_source_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningNearest.run_source_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.summand_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.bids_context_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseFirst_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate.updatedBudget_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryRawOpening_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.result_success_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.fair_zero_completion_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.successful_completion_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K017
import Definitions.Def_Q238K018
import Definitions.Def_Q238K019
import Definitions.Def_Q238K020
import Definitions.Def_Q238K021

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace BinaryOpeningActivity
open WordList

def context {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v z : ℚ) (j : Fin d) : List Bool :=
  pairBits (pairBits (Rectangular.encode distance,j.val.bits),
    pairBits (BinaryRational.encode v,BinaryRational.encode z))
end BinaryOpeningActivity
end
open WordOperations BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RowInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFirst
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalOpenability
open BinaryOpeningPayment

def context {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam : ℚ) : List Bool := encode [Rectangular.encode distance,
      BinaryOpeningActivity.indices ((subtypeList W).map Subtype.val),BinaryRational.encode v,
      BinaryRational.encode z,BinaryRational.encode lam,BinaryRational.encode 0,[],
      List.replicate d true,BinaryOpeningActivity.indices ((subtypeList F).map Subtype.val)]
def resultBits {m d : ℕ} : Option (RationalPhase.Event m d) → List Bool
  | none=>[]
  | some e=>true::eventBits e
end MetricKMedianRecovery.BitMachine.BinaryPhaseFirst

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q a T L : ℕ}
noncomputable def bagWords (x : List Bool) : List Bool :=
  filterWith bagTest (pairBits (x,Indices.run (field 3 (extractPrefix x))))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalLeaves
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [PseudoMetricSpace V]

attribute [local instance] metric

variable [DecidableEq V]

def copy (key : ℕ) : Label V → Label V :=
  Sum.elim (fun i=>leaf key i 0) Sum.inr

def shorten (key : ℕ) (i : V) (l u : ℚ) : Label V → Label V :=
  Equiv.swap (leaf key i u) (leaf key i l)

end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LeafOrder
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [DecidableEq V] {d : ℕ}

def Correction.apply : Correction V → Label V → Label V
  | .identity => id
  | .shorten key i l u => RationalLeaves.shorten key i l u

def State.mapPrefix (s : State V) := s.P.map (List.map s.correction.apply)
def State.mapFree (s : State V) := s.B.image s.correction.apply

attribute [local instance] RationalLeaves.metric

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FiniteContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open Classical
open WordOperations WordList BinaryOpeningPayment RationalLeaves
open BinaryLabel (orderedSort)

def pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) : List Bool :=
  encode [Rectangular.encode distance,List.replicate d true,setBits F,setBits Q,
    labels (List.ofFn loc),BinaryRational.encode v,BinaryRational.encode z,BinaryRational.encode lam]
attribute [local irreducible] BinaryLabelMatrix.run
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_StateBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase
open BinaryOpeningPayment

def stateBits {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : List Bool :=
  pairBits (BinaryPhaseFirst.context distance F s.opened v s.phase lam,
    RationalMatrix.rowEncode (fun j=>s.budget[j]))
end MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseTrace
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
def pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (es : List (Event m d)) : List Bool :=
  pairBits (stateBits distance F v lam s,encode (es.map BinaryPhaseFirst.eventBits))
end MetricKMedianRecovery.BitMachine.BinaryPhaseTrace

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Min
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic WordList
namespace BinaryPhaseAdvance
open EffectiveOpenability RationalPhase BinaryPhaseUpdate BinaryOpeningPayment

noncomputable def isActive (x : List Bool) : Bool := BinaryOpeningPayment.active (query x)
noncomputable def budgetItem (x : List Bool) : List Bool :=
  if isActive x then BinaryRational.encode (clippedItem x)
  else Lookup.run (pairBits (discardPrefix x,discardPrefix (extractPrefix x)))
noncomputable def budget (x : List Bool) : List Bool :=
  mapWith budgetItem (pairBits (x,BinaryOpeningEnumeration.clients (extractPrefix x)))
noncomputable def run (x : List Bool) : List Bool := pairBits (context x,budget x)
end BinaryPhaseAdvance
end MetricKMedianRecovery.BitMachine

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
def pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (hs : List (List (Fin m))) : List Bool :=
  pairBits (stateBits distance F v lam s,historyBits hs)
end MetricKMedianRecovery.BitMachine.BinaryHistoryRun

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_FiniteMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteMachine
open WordOperations WordList RationalLeaves PhaseSequence
open BinaryFiniteContext (labels setBits)
noncomputable def after (x : List Bool) : List Bool :=
  BinaryLabel.sort (extractPrefix x++Flatten.run (discardPrefix x))
end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordExtras
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field )
noncomputable def source (x : List Bool) : List Bool :=
  if tagIs 0 x then cf 3 x else jf 1 x++cons (if tagIs 1 x then jf 4 x else copied x) (jf 2 x)
noncomputable def target (x : List Bool) : List Bool :=
  if tagIs 0 x then cf 3 x++cons (copied x) [] else
    if tagIs 1 x then (jf 1 x++jf 2 x)++jf 3 x else jf 1 x++cons (jf 4 x) (jf 2 x)
noncomputable def accepts (x : List Bool) : Bool :=
  WordEq.eq (pairBits (source x,cf 3 x)) && (WordEq.eq (pairBits (target x,cf 4 x)) &&
    (BinaryLabel.contains (pairBits (jf 4 x,cf 0 x)) &&
      labelsCheck x))

end MetricKMedianRecovery.BitMachine.BinaryJump

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalRawPrep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionFill
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q a : ℕ}
noncomputable def options (x : List Bool) : List Bool :=
  filterWith test (pairBits (encode [field 0 (extractPrefix x),discardPrefix x],field 2 (extractPrefix x)))
noncomputable def pick (x : List Bool) : List Bool :=
  if options x=[] then Lookup.run (pairBits (discardPrefix x,field 1 (extractPrefix x))) else WordList.head (options x)
attribute [local irreducible] options

noncomputable def run (x : List Bool) : List Bool := mapWith pick (pairBits (x,Indices.run (field 1 x)))
end MetricKMedianRecovery.BitMachine.BinaryCompletionFill

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ListSetExtra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Set
open WordOperations BinaryArithmetic
noncomputable def pack_computes {xs j v : List Bool→List Bool}
    (hx : PolyComputes xs) (hj : PolyComputes j) (hv : PolyComputes v) :
    PolyComputes (fun x=>pack (xs x) (j x) (v x)) := hx.pair (hj.pair hv)
end MetricKMedianRecovery.BitMachine.WordList.Set

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
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def output (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (q : ℕ)
    (bits : Categorical.BinaryOracleIndex (Fin (s.leaves.length*n)) s.leaves.length (Categorical.Explicit.exponent s.leaves.length)
      (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length)→Bool) : Finset (Fin n) := by
  classical
  exact if hr : BinaryBranchCheck.Ready δ F S s colors q 0 0 then
    result δ D F S Δ s colors hr.2.1 (Fin.elim0 : Fin 0→Fin n) Fin.elim0 q bits
  else S
end MetricKMedianRecovery.BitMachine.BinaryZeroBranch

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
abbrev Seed (n p : ℕ) := (Fin n→Fin 4)×BinaryObservableBranch.Bits n p
def embed {n p : ℕ} (seed : Seed n p) : BinaryBranchTape.Seed n 1 p := ((seed.1,fun _=>⟨0,by unfold ColorLabel.labelRange; positivity⟩),seed.2)
def raw {n p : ℕ} (seed : Seed n p) : List Bool := BinaryBranchTape.raw (embed seed)
abbrev count (n p : ℕ) := BinaryBranchTape.colorCount n+BinaryBranchTape.completionCount n p
def layout (n p : ℕ) : (Fin (count n p)→Bool)≃Seed n p :=
  (BinaryBranchTape.split _ _).trans (Equiv.prodCongr (BinaryBranchTape.colors n)
    (BinaryCategorical.Tape.layout (p*n) p (Categorical.Explicit.exponent p) (Categorical.Explicit.samples (p*n) p)))
end MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricCost2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricBest
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def run (x : List Bool) : List Bool := BinaryRationalBest.run score x
end MetricKMedianRecovery.BitMachine.BinaryMetricBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchTapeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchTape
attribute [local irreducible] Categorical.Explicit.exponent Categorical.Explicit.samples Categorical.Explicit.steps
lemma count_bound {n b p H : ℕ} (hn : n≤H) (hb : b≤H) (hp : p≤H) :
    count n b p ≤ 201326592000000015*(H+2)^12 := by
  let X := H+2
  have hX : 1≤X := by dsimp [X]; omega
  have hnX : n≤X := hn.trans (by dsimp [X];omega)
  have hbX : b≤X := hb.trans (by dsimp [X];omega)
  have hpX : p≤X := hp.trans (by dsimp [X];omega)
  have hpn : p*n≤X^2 := by
    calc p*n≤X*X := Nat.mul_le_mul hpX hnX
         _=X^2 := by ring
  have hpn1 : p*n+1≤X^2 := by
    have hh:=Nat.mul_le_mul hp hn
    dsimp [X]
    nlinarith
  have hstep : Categorical.Explicit.steps p≤4096*X^2 :=
    (Categorical.Explicit.steps_upper p).trans (by dsimp [X];gcongr)
  have hexp : Categorical.Explicit.exponent p≤12*X := by
    have hr : (p+1).size≤p+1 := Nat.size_le.mpr Nat.lt_two_pow_self
    unfold Categorical.Explicit.exponent
    dsimp [X]
    omega
  have hp1 : p+1≤X := by dsimp [X];omega
  have hsamp : Categorical.Explicit.samples (p*n) p≤4096000000000*X^6 := by
    unfold Categorical.Explicit.samples
    calc
      _ ≤ 1000000000*(4096*X^2)*X^2*X^2 := by gcongr
      _ = _ := by ring
  have hm : BinaryCategorical.Tape.M (p*n) p (Categorical.Explicit.exponent p)
      (Categorical.Explicit.samples (p*n) p) ≤ 201326592000000000*X^12 := by
    unfold BinaryCategorical.Tape.M BinarySeed.count
    change 2^Categorical.Explicit.exponent p*((p*n)*(Categorical.Explicit.samples (p*n) p*(p*Categorical.Explicit.exponent p))) ≤ _
    rw [←Categorical.Explicit.steps]
    calc
      _ ≤ (4096*X^2)*(X^2*((4096000000000*X^6)*(X*(12*X)))) := by gcongr
      _ = _ := by ring
  have hk : BinaryCategorical.Tape.K p (Categorical.Explicit.exponent p)≤12*X^2 := by
    unfold BinaryCategorical.Tape.K BinarySeed.count
    calc p*Categorical.Explicit.exponent p≤X*(12*X) := Nat.mul_le_mul hpX hexp
         _=12*X^2 := by ring
  have hl : labelCount n b≤X^2 := by
    unfold labelCount
    calc n*Nat.clog 2 b≤X*X := Nat.mul_le_mul hnX ((Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n:=b)).le).trans hbX)
         _=X^2 := by ring
  have hc : colorCount n≤2*X := by unfold colorCount;omega
  have hpow1 : X≤X^12 := by
    calc X=X^1 := by simp
         _≤X^12 := Nat.pow_le_pow_right hX (by decide)
  have hpow2 : X^2≤X^12 := Nat.pow_le_pow_right hX (by decide)
  unfold count completionCount
  dsimp [X] at *
  omega
end MetricKMedianRecovery.BitMachine.BinaryBranchTape

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_RecoveryTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryBranchTape
open BinaryOpeningPayment (field )
attribute [local irreducible] zeroContext
  BinaryObservableBranch.output BinaryZeroBranch.output ColorLabel.label ColorLabel.color
  BinaryBranchTape.layout BinaryRandomizedZeroBranch.layout
def positiveSeed {n m p H : ℕ} (hn : n≤H) (hm : m≤H) (hp : p≤H) (b : Fin m)
    (seed : Fin (tapeSize H)→Bool) : BinaryBranchTape.Seed n (b.val+1) p :=
  BinaryBranchTape.layout n (b.val+1) p (fun i=>seed (Fin.castLE
    (BinaryBranchTape.count_bound hn ((Nat.succ_le_of_lt b.isLt).trans hm) hp) i))
lemma zeroCount_bound {n p H : ℕ} (hn : n≤H) (hH : 1≤H) (hp : p≤H) :
    BinaryRandomizedZeroBranch.count n p≤tapeSize H := by
  simpa only [tapeSize,BinaryRandomizedZeroBranch.count,count,labelCount,Nat.clog_one_right,Nat.mul_zero,Nat.add_zero]
    using BinaryBranchTape.count_bound hn hH hp
def zeroSeed {n p H : ℕ} (hn : n≤H) (hH : 1≤H) (hp : p≤H)
    (seed : Fin (tapeSize H)→Bool) : BinaryRandomizedZeroBranch.Seed n p :=
  BinaryRandomizedZeroBranch.layout n p (fun i=>seed (Fin.castLE (zeroCount_bound hn hH hp) i))
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RecoveryCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryBranchTape Completion FiniteSampling
variable {n m H : ℕ}
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
  (s : RationalSampling.State n) (hn : n≤H) (hm : m≤H) (hH : 1≤H)
  (hp : s.leaves.length≤H) (r0 y0 : Fin n) (seed : Fin (tapeSize H)→Bool)
noncomputable def positive (q c : Fin (n+1)) (b : Fin m) : Finset (Fin n) :=
  let z:=positiveSeed hn hm hp b seed
  BinaryObservableBranch.output δ D F S Δ s (fun i=>ColorLabel.color (z.1.1 i))
    (fun i=>ColorLabel.label (b.val+1) (by omega) (z.1.2 i)) q.val c.val r0 y0 z.2
noncomputable def zero (q : Fin (n+1)) : Finset (Fin n) :=
  let z:=zeroSeed hn hH hp seed
  BinaryZeroBranch.output δ D F S Δ s (fun i=>ColorLabel.color (z.1 i)) q.val z.2
noncomputable def candidates : List (Finset (Fin n)) :=
  List.ofFn (zero δ D F S Δ s hn hH hp seed) ++
    (List.ofFn (fun q:Fin (n+1)=>q)).flatMap (fun q=>(List.ofFn (fun c:Fin (n+1)=>c)).flatMap
      (fun c=>List.ofFn (fun b:Fin m=>positive δ D F S Δ s hn hm hp r0 y0 seed q c b)))
noncomputable def result : Finset (Fin n) :=
  BinaryMetricBest.best δ D S (candidates δ D F S Δ s hn hm hH hp r0 y0 seed)
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoverySemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery
open WordOperations WordList Sampling.Comparison
variable {n : ℕ}
noncomputable def stateAt (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (seed : Fin (2*m)→Fin (integralPrecision D (Δ:ℝ) m)→Bool) (i : Fin (2*m+1)) :
    Option (RationalSampling.State n) :=
  ((List.ofFn seed).take i.val).foldl
    (RationalSampling.next δ D F S Δ P (1/1000000) m BinarySampler.Parameters.M BinarySampler.Parameters.E
      (RadiusMenus.thirdSize mainKappa m) (integralPrecision D (Δ:ℝ) m)) (some RationalSampling.State.initial)
noncomputable def optionOutput (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (m : ℕ) (hm : m≤n)
    (r0 y0 : Fin n) (seed : Fin (BinaryRecovery.tapeSize (n+1))→Bool) (w : Option (RationalSampling.State n)) :
    Finset (Fin n) :=
  w.elim S (fun s=>if hp:s.leaves.length≤n+1 then
    BinaryRecovery.result δ D F S Δ s (Nat.le_succ n) (hm.trans (Nat.le_succ n)) (by omega) hp r0 y0 seed else S)
noncomputable def candidates (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ) (hm : m≤n)
    (r0 y0 : Fin n) (sample : Fin (2*m)→Fin (integralPrecision D (Δ:ℝ) m)→Bool)
    (complete : Fin (BinaryRecovery.tapeSize (n+1))→Bool) : List (Finset (Fin n)) :=
  List.ofFn (fun i=>optionOutput δ D F S Δ m hm r0 y0 complete (stateAt δ D F S Δ P m sample i))
noncomputable def result (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ) (hm : m≤n)
    (r0 y0 : Fin n) (sample : Fin (2*m)→Fin (integralPrecision D (Δ:ℝ) m)→Bool)
    (complete : Fin (BinaryRecovery.tapeSize (n+1))→Bool) : Finset (Fin n) :=
  BinaryMetricBest.best δ D S (candidates δ D F S Δ P m hm r0 y0 sample complete)
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
attribute [local irreducible] raw extra RawDrop.run
noncomputable def count {n : ℕ} (D : Finset (Fin n)) (Δ m : ℕ) : ℕ :=
  2*m*integralPrecision D (Δ:ℝ) m+BinaryRecovery.tapeSize (n+1)
noncomputable def layout {n : ℕ} (D : Finset (Fin n)) (Δ m : ℕ) :
    (Fin (count D Δ m)→Bool)≃(Fin (2*m)→Fin (integralPrecision D (Δ:ℝ) m)→Bool)×
      (Fin (BinaryRecovery.tapeSize (n+1))→Bool) :=
  (BinaryBranchTape.split (2*m*integralPrecision D (Δ:ℝ) m) (BinaryRecovery.tapeSize (n+1))).trans
    (Equiv.prodCongr (BinarySeed.tensorEquiv [2*m] (integralPrecision D (Δ:ℝ) m)) (Equiv.refl _))
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
open Completion Sampling Sampling.Comparison FiniteSampling
variable {n : ℕ}
noncomputable def output (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (hm : m≤n) (r0 y0 : Fin n) (seed : Fin (count D Δ m)→Bool) : Finset (Fin n) :=
  BinaryIntegralRecovery.result δ D F S Δ P m hm r0 y0 (layout D Δ m seed).1 (layout D Δ m seed).2
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
attribute [local irreducible] extra Fair.raw BinaryMetricBest.run RawUnary.run BinaryIntegralRecovery.result BinaryFinSet.encode BinarySampler.Parameters.pack BinaryMetricBest.best Fair.output List.ofFn BinarySeed.raw
attribute [local irreducible] mapWith
variable {n : ℕ}
noncomputable def output (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (hm : m≤n) (r0 y0 : Fin n) (t : ℕ) (seed : Fin t→Fin (Fair.count D Δ m)→Bool) : Finset (Fin n) :=
  BinaryMetricBest.best δ D S (List.ofFn (fun i=>Fair.output δ D F S Δ P m hm r0 y0 (seed i)))
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat

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
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
def encode {m : ℕ} : Correction (Fin m) → List Bool
  | .identity => []
  | .shorten key i l u => pairBits (BinaryLabel.encode (leaf key i u),BinaryLabel.encode (leaf key i l))
noncomputable def mapSet : List Bool→List Bool := BinaryLabel.sort ∘ mapRow
end MetricKMedianRecovery.BitMachine.BinaryCorrection

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
def stateBits {m : ℕ} (s : State (Fin m)) : List Bool :=
  encode [setBits s.B,historyBits s.P,BinaryCorrection.encode s.correction,
    BinaryRational.encode s.lam,BinaryRational.encode s.lam',historyBits s.T,historyBits s.U]
def outcomeBits {m : ℕ} : Outcome (Fin m)→List Bool
 | .inl o=>pairBits ([],outputBits o)
 | .inr s=>pairBits ([true],stateBits s)
noncomputable def mapFree (x : List Bool) : List Bool := BinaryCorrection.mapSet (pairBits (field 2 x,field 0 x))
attribute [local irreducible] BinaryCorrection.mapHistory
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_DuplicateMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix
open WordOperations WordList
variable {n : ℕ}
noncomputable def twice_computes : PolyComputes twice := id_computes.append id_computes

end MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LengthEncode
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLength
open WordOperations WordList RationalLeaves CanonicalLengthView BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field )
attribute [local irreducible] BinaryLabelMatrix.row
def ctxBits {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Label (Fin m)))
    (R H G : List (Label (Fin m))) : List Bool :=
  encode [setBits F,labels R,labels H,labels G,pairBits (Rectangular.encode distance,List.replicate d true)]
noncomputable def rootIn (x : List Bool) : Bool := BinaryLabel.contains (pairBits (pf 1 x,cf 0 x))
noncomputable def freeOut (x : List Bool) : Bool := !BinaryLabel.contains (pairBits (pf 2 x,cf 0 x))
noncomputable def row (n : ℕ) (x : List Bool) : List Bool := BinaryLabelMatrix.row (pairBits (cf 4 x,pf n x))
noncomputable def sameRow (x : List Bool) : Bool := WordEq.eq (pairBits (row 1 x,row 2 x))
noncomputable def extra (x : List Bool) : Bool := if isFree x then freeOut x && sameRow x else true
noncomputable def accepts (x : List Bool) : Bool := rootIn x &&
  (WordEq.eq (pairBits (cf 2 x,source x)) && (WordEq.eq (pairBits (cf 3 x,target x)) && extra x))
end MetricKMedianRecovery.BitMachine.BinaryLength

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
noncomputable def inter (x : List Bool) : List Bool :=
  BinaryLabel.sort (filterWith containsItem (pairBits (discardPrefix x,extractPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

namespace MetricKMedianRecovery.BitMachine.BinaryCross
open WordOperations WordList RationalLeaves BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field )

noncomputable def opened (x : List Bool) : List Bool := BinaryFiniteContext.union
  (pairBits (cf 1 x,extractPrefix (discardPrefix x)))
noncomputable def finalOpened (x : List Bool) : List Bool :=
  BinaryFiniteMachine.after (pairBits (opened x,discardPrefix (discardPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryCross

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
open BinaryOpeningPayment (field )
noncomputable def opened (x : List Bool) : List Bool :=
  BinaryFiniteContext.union (pairBits (field 3 (cf 0 x),WordList.cons (newLeaf x) []))
noncomputable def base (x : List Bool) : List Bool := BinaryFiniteContext.replaceOpen (pairBits (cf 0 x,opened x))
end MetricKMedianRecovery.BitMachine.BinaryLengthQuery

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
open BinaryOpeningPayment (field )

noncomputable def opened (x : List Bool) : List Bool := BinaryFiniteContext.union (pairBits (field 3 (field 0 x),common x))
noncomputable def base (x : List Bool) : List Bool := BinaryFiniteContext.replaceOpen (pairBits (field 0 x,opened x))
noncomputable def context (x : List Bool) : List Bool := encode [base x,field 1 x,nextQ x,field 3 x,jf 1 x,field 4 x,small x,large x]
noncomputable def searchInput (x : List Bool) : List Bool := encode [field 6 x,context x,field 5 x,BinaryRational.encode 0,field 4 x]
noncomputable def atZero (x : List Bool) : List Bool := pairBits (context x,BinaryRational.encode 0)
end MetricKMedianRecovery.BitMachine.BinarySensitive

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_StateBits2
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledState
open WordOperations WordList RationalLeaves RationalHeight CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

def encode {m : ℕ} (s : State (Fin m)) : List Bool := WordList.encode
  [setBits s.B,setBits s.mapFree,historyBits s.P,historyBits s.mapPrefix,
    BinaryRational.encode s.lam,BinaryRational.encode s.lam',historyBits s.T,historyBits s.U]

end MetricKMedianRecovery.BitMachine.BinaryCoupledState

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
open BinaryOpeningPayment (field )
noncomputable def addOne (x : List Bool) : List Bool := BinaryLabel.sort (cons (extractPrefix x) (discardPrefix x))

noncomputable def without (x : List Bool) : Bool := !BinaryLabel.contains (swapWords x)
noncomputable def diff (x : List Bool) : List Bool := BinaryLabel.sort (filterWith without (swapWords x))
noncomputable def insertEach : List Bool→List Bool := mapWith addOne ∘ swapWords
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
noncomputable def widths (w : ℕ) : List Bool→List Bool :=
  match w with
  | 0=>fun _=>encode [[]]
  | w+1=>fun x=>widths w x++flatMapWith insertEach (pairBits (widths w x,x))
noncomputable def removed (w : ℕ) (x : List Bool) : List Bool :=
  mapWith diff (pairBits (discardPrefix x,widths w (extractPrefix x)))
noncomputable def raw (w : ℕ) (x : List Bool) : List Bool :=
  crossWith BinaryFiniteContext.union (pairBits (removed w x,widths w (extractPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryLocalCandidates

namespace MetricKMedianRecovery.BitMachine.BinaryLocalCost
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field )
noncomputable def entry (x : List Bool) : List Bool :=
  BinaryLabel.row (pairBits (pairBits (extractPrefix (extractPrefix x),discardPrefix x),discardPrefix (extractPrefix x)))
noncomputable def near (x : List Bool) : List Bool := RationalMin.run
  (mapWith entry (pairBits (pairBits (field 0 (extractPrefix x),discardPrefix x),field 2 (extractPrefix x))))
def pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (S : Finset (Label (Fin m))) : List Bool :=
  encode [Rectangular.encode distance,List.replicate d true,setBits S]
noncomputable def run (x : List Bool) : List Bool := RationalArray.sumWords
  (mapWith near (pairBits (x,BinaryEllipsoidInitial.indices (field 1 x))))
noncomputable def rank (x : List Bool) : List Bool := (⌈BinaryRational.decode (run x)⌉₊).bits
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

namespace MetricKMedianRecovery.BitMachine.BinaryLocalSearch
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field )
def pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Label (Fin m))) (S : Finset (Label (Fin m))) : List Bool :=
  encode [Rectangular.encode distance,List.replicate d true,labels fs,setBits S]
noncomputable def rank (x : List Bool) : List Bool := BinaryLocalCost.rank
  (encode [field 0 (extractPrefix x),field 1 (extractPrefix x),discardPrefix x])
end MetricKMedianRecovery.BitMachine.BinaryLocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalFuel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalAnchor
open WordOperations WordList BinaryArithmetic RationalLeaves Polynomial
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field )
attribute [local irreducible] BinaryLabel.sort
def pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Fin m)) (r : ℕ) : List Bool :=
  encode [Rectangular.encode distance,List.replicate d true,labels (fs.map original),r.bits]
end MetricKMedianRecovery.BitMachine.BinaryLocalAnchor

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
def pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Fin m)) (S : Finset (Fin m)) : List Bool :=
  BinaryLocalSearch.pack distance (fs.map original) (S.image original)
end MetricKMedianRecovery.BitMachine.BinaryLocalRefine

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
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
noncomputable def leafBank (x : List Bool) : List Bool := BinaryFiniteContext.union (pairBits (field 0 x,cons (endLeaf 7 x) []))
noncomputable def leafResult (x : List Bool) : List Bool :=
  encode [leafBank x,leafPrefix x,pairBits (endLeaf 7 x,endLeaf 6 x),field 2 x,field 2 x,field 8 x,field 9 x]
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_PlanResult
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPlanResult
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge CanonicalLengthView
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

noncomputable def finishInput (x : List Bool) : List Bool :=
  encode [BinaryCoupled.leafBank (leafInput x),price x,BinaryCoupled.leafPrefix (leafInput x),rf 3 x]
noncomputable def run (x : List Bool) : List Bool := if success x then
  pairBits ([],BinaryCoupled.finish (finishInput x)) else pairBits ([true],BinaryCoupled.leafResult (leafInput x))
def pack {m : ℕ} (sensitive : List Bool) (B : Finset (Label (Fin m))) (P : List (List (Label (Fin m))))
    (R : CanonicalLengthSearch.Result (Label (Fin m))) : List Bool := encode [sensitive,setBits B,historyBits P,BinaryLengthSearch.resultBits R]
end MetricKMedianRecovery.BitMachine.BinaryPlanResult

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field )
noncomputable def copiedSet (x : List Bool) : List Bool := BinaryLabel.sort (mapWith BinaryLabel.copied x)
noncomputable def pool (x : List Bool) : List Bool := union (pairBits (field 1 x,copiedSet (pairBits (field 2 x,field 0 x))))
noncomputable def bankFirst (x : List Bool) : List Bool := pool (encode [field 0 x,field 1 x,threeQ x])
noncomputable def banks (x : List Bool) : List Bool := pool (encode [field 0 x,bankFirst x,threeQOne x])
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

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
open BinaryOpeningPayment (field )

def contextBits (base : List Bool) (key : ℕ) {m : ℕ} (F : Finset (Label (Fin m))) :=
  encode [base,key.bits,labels ((BinaryLabel.orderedSort F).map (copy key))]
noncomputable def copied (x : List Bool) : List Bool := BinaryLabel.copied (pairBits (cf 1 x,item x))
attribute [local irreducible] BinaryLabel.copied
noncomputable def advancingInput (x : List Bool) : List Bool :=
  encode [cf 0 x,sf 0 x,sf 1 x,item x,copied x]
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

def pack {m : ℕ} (base : List Bool) (key : ℕ) (F : Finset (Label (Fin m)))
    (C U T : List (Label (Fin m))) : List Bool :=
  Fold.pack (labels T) (contextBits base key F) (accBits ⟨C,U,[]⟩)
end MetricKMedianRecovery.BitMachine.BinaryMatch

namespace MetricKMedianRecovery.BitMachine.BinaryRegular
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field )

noncomputable def pool : List Bool → List Bool := mapWith BinaryLabel.copied ∘ poolInput
noncomputable def context (x : List Bool) : List Bool := encode [field 0 x,field 1 x,pool x]
noncomputable def matchInput (x : List Bool) : List Bool := Fold.pack (field 2 x) (context x) (state0 x)
end MetricKMedianRecovery.BitMachine.BinaryRegular

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RefineMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field )
noncomputable def ctSpare (x : List Bool) : List Bool := ct x++cons (spareWord x) []
end MetricKMedianRecovery.BitMachine.BinaryJump

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
open BinaryOpeningPayment (field )
noncomputable def opened (x : List Bool) : List Bool :=
  BinaryFiniteContext.union (pairBits (field 3 (cf 0 x),discardPrefix x))
noncomputable def base (x : List Bool) : List Bool := BinaryFiniteContext.replaceOpen (pairBits (cf 0 x,opened x))
noncomputable def contInput (x : List Bool) : List Bool := pairBits (cf 1 x,pairBits (cf 2 x,base x))
def pack {m : ℕ} (base : List Bool) (F Q : Finset (Label (Fin m))) (k n q : ℕ)
    (U : List (List (Label (Fin m)))) (H : List (Label (Fin m))) (T S : List (List (Label (Fin m)))) : List Bool :=
  encode [base,List.replicate n true,List.replicate q true,ctxBits F Q k,historyBits U,nodeBits (H,T),historyBits S]
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
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outcomeBits)
def pack {m : ℕ} (base : List Bool) (n q : ℕ) (b : ℚ) (precision k : ℕ) (s : State (Fin m)) : List Bool :=
  encode [base,List.replicate n true,List.replicate q true,BinaryRational.encode b,List.replicate precision true,k.bits,stateBits s]
noncomputable def mappedFree (x : List Bool) : List Bool := BinaryCoupled.mapFree (field 6 x)
noncomputable def Q (x : List Bool) : List Bool := BinaryFiniteMachine.after (pairBits ([],mappedPrefix x))
noncomputable def QG (x : List Bool) : List Bool := BinaryFiniteContext.union (pairBits (Q x,G x))
noncomputable def ctx (x : List Bool) : List Bool := encode [bf 2 x,Q x,field 5 x]
noncomputable def bankInput (x : List Bool) : List Bool := encode [bf 2 x,mappedFree x,qbits x]
noncomputable def banks (x : List Bool) : List Bool := BinaryFiniteContext.banks (bankInput x)
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
open BinaryOpeningPayment (field )
open BinaryCoupled (stateBits outcomeBits outputBits)
def pack (base : List Bool) (b : ℚ) (precision k : ℕ) {m : ℕ} (f : Frame (Fin m)) : List Bool :=
  encode [base,List.replicate f.n true,List.replicate f.q true,BinaryRational.encode b,
    List.replicate precision true,k.bits,outcomeBits f.out]
attribute [local instance] RationalLeaves.metric
end MetricKMedianRecovery.BitMachine.BinaryCoupledLoop

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
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outputBits)
def pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (F : Finset (Fin m)) (v lo M : ℚ) (N precision total k : ℕ) : List Bool :=
  encode [BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) ∅ v 0 0,
    List.replicate N true,List.replicate precision true,List.replicate total true,k.bits,
    BinaryRational.encode lo,BinaryRational.encode M]

end MetricKMedianRecovery.BitMachine.BinaryInitial

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
noncomputable def lift (x : List Bool) : List Bool :=
  BinaryLabel.sort (WordList.map originalWord x)
end MetricKMedianRecovery.BitMachine.BinaryProjection

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
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
noncomputable def context (v : ℚ) (x : List Bool) : List Bool :=
  encode [field 0 x,field 1 x,BinaryProjection.lift (field 2 x),[],
    map BinaryProjection.originalWord (field 3 x),BinaryRational.encode v,BinaryRational.encode 0,BinaryRational.encode 0]
end MetricKMedianRecovery.BitMachine.BinaryInitialAuto

end OAI
end


