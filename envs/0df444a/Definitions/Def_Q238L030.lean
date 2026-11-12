-- Prove2me | Definitions.Def_Q238L030
-- name    : Q238L030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:28:30.728801+00:00
-- url     : https://prove2.me/theorems/81f5cd68-e399-4d74-b4d7-c232af26c34f
-- title:
--   Definitions bundle Q238L030 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 81 declarations of OpenAI's Lean: 79 definitions and 2 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.scales`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.one`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.rowRun`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.values`, `OAI.MetricKMedianRecovery.BitMachine.BinaryHistoryRun.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.output`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows.offset`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.R.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.count`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.layout`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.sizeWord`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.output`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.candidates`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.optionOutput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.result`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.ctxBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLength.ctxBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.ctxBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLengthSearch.resultBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalCost.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalSearch.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMaskParser.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.accBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.index`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.uniformRadius`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricArrays.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricBest.context`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricCost.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNodeScan.pack` and 39 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_GlobalCall`, `KMedianRecovery_Algorithms_GlobalOuter`, `KMedianRecovery_Algorithms_GlobalZero`, `KMedianRecovery_Algorithms_IntegralRecoveryAll`, `KMedianRecovery_Algorithms_IntegralRecoveryDemand`, `KMedianRecovery_Algorithms_IntegralRecoveryGuesses`, `KMedianRecovery_Algorithms_IntegralRecoveryMachine`, `KMedianRecovery_Algorithms_IntegralRecoveryRepeat`, `KMedianRecovery_Algorithms_IntegralRecoverySemantics`, `KMedianRecovery_Algorithms_IntegralRecoverySuccess`, `KMedianRecovery_Branching_PopulationMachine`, `KMedianRecovery_Encoding_FinSets`, `KMedianRecovery_Encoding_HistoryBits`, `KMedianRecovery_Encoding_LengthEncode`, `KMedianRecovery_Encoding_MatrixRows`, `KMedianRecovery_Encoding_StateBits`, `KMedianRecovery_Encoding_UnaryParser`, `KMedianRecovery_Encoding_WordExtras`, `KMedianRecovery_Geometry_LocalBest`, `KMedianRecovery_Geometry_LocalCandidates`, `KMedianRecovery_Geometry_LocalFuel`, `KMedianRecovery_Geometry_LocalRefineMachine`, `KMedianRecovery_Geometry_MetricAnchor`, `KMedianRecovery_Geometry_MetricArrays`, `KMedianRecovery_Geometry_MetricCost2`, `KMedianRecovery_Geometry_RoundingMatrix`, `KMedianRecovery_Machines_InitialLoop`, `KMedianRecovery_Machines_LengthQuery`, `KMedianRecovery_Machines_MatchFold`, `KMedianRecovery_Machines_MatchSize`, `KMedianRecovery_Machines_MenuMachine`, `KMedianRecovery_Machines_NormalizationMachine`, `KMedianRecovery_Machines_RecoveryTape`, `KMedianRecovery_Machines_ResolveMachine`, `KMedianRecovery_Machines_SensitiveMachine`, `KMedianRecovery_Recovery_Basic`, `KMedianRecovery_Recovery_BoundedDecision`, `KMedianRecovery_Recovery_FinImages`, `KMedianRecovery_Recovery_FirstPresent`, `KMedianRecovery_Recovery_Pack10`, `KMedianRecovery_Recovery_Pack11`, `KMedianRecovery_Recovery_PlanResult`, `KMedianRecovery_Recovery_RecoveryCandidates`, `KMedianRecovery_Recovery_RowInput`, `KMedianRecovery_Recovery_Values`, `KMedianRecovery_Sampling_SamplerParameters`, `KMedianRecovery_Sampling_SamplingStateMachine`, `KMedianRecovery_Strictness_MetricSurplus`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L022`, `Q238L023`, `Q238L024`, `Q238L025` and `Q238L026` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q238L035`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.gram_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.rhs_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.transposed_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.extract_output_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output_success_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.amplified_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.view_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLength.view_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.integral_spec_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalSearch.iterate_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.anchorInput_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricBest.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.coefficient_source_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningNearest.run_source_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.sumWords_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.summand_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.answer_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.bids_context_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseTrace.iterate_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate.updatedBudget_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.prepared_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.rowCoefficients_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.rowWord_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.result_success_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.remove_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.localInput_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryTaggedSets.unshift_encode_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.gram_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.rhs_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.transposed_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.extract_output_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output_success_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.amplified_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.view_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLength.view_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.integral_spec_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalSearch.iterate_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.anchorInput_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricBest.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.coefficient_source_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningNearest.run_source_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.sumWords_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.summand_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.answer_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.bids_context_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseTrace.iterate_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate.updatedBudget_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.prepared_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.rowCoefficients_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.rowWord_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.result_success_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRefine.cutOp_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.remove_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.integral_spec_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.localInput_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryTaggedSets.unshift_encode_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L022
import Definitions.Def_Q238L023
import Definitions.Def_Q238L024
import Definitions.Def_Q238L025
import Definitions.Def_Q238L026

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundedDecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

namespace BinaryRationalDecision
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList

def pack {n : ℕ} (rs : List (Row n)) (B : ℕ) : List Bool :=
  pairBits (List.replicate n true,pairBits (List.replicate rs.length true,
    pairBits (B.bits,BinaryRow.rowsEncode rs)))
end BinaryRationalDecision

open WordOperations
end MetricKMedianRecovery.BitMachine

end OAI
end

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Values
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryOpeningPayment
open WordList RationalLinearFeasibility

def pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : List Bool :=
  WordList.encode [Rectangular.encode distance,
    BinaryOpeningActivity.indices ((EffectiveOpenability.subtypeList W).map Subtype.val),
    BinaryRational.encode v,BinaryRational.encode z,BinaryRational.encode lam,
    BinaryRational.encode eta,i.val.bits,List.replicate d true,
    BinaryOpeningActivity.indices ((EffectiveOpenability.subtypeList F).map Subtype.val)]
end BinaryOpeningPayment
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack10
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryOpeningOracle
open WordOperations BinaryArithmetic RationalLinearFeasibility RationalOpenability
open EffectiveOpenability BinaryExactSolve

def pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : List Bool :=
  BinaryRationalDecision.pack
    ((kindRows (List.ofFn (fun j : Fin d=>j)) (subtypeList W) (subtypeList F)).map
      (fun r=>(forms distance F W v z lam eta i r).enumeratedRow (variableEnum d F)))
    ⌈(1+v^2)*z⌉₊

def resultBits {m d : ℕ} (F : Finset (Fin m)) :
    Option (Variables (Fin d) F → ℚ) → List Bool
  | none=>[]
  | some x=>true::RationalMatrix.rowEncode (fun j=>x (variableEnum d F j))

end MetricKMedianRecovery.BitMachine.BinaryOpeningOracle

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

def eventBits {m d : ℕ} (e : RationalPhase.Event m d) : List Bool :=
  pairBits (e.facility.val.bits,RationalMatrix.rowEncode (fun j=>e.bid[j]))
def resultBits {m d : ℕ} : Option (RationalPhase.Event m d) → List Bool
  | none=>[]
  | some e=>true::eventBits e
end MetricKMedianRecovery.BitMachine.BinaryPhaseFirst

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordExtras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_encode)
def ctxBits {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key : ℕ)
    (H G : List (Label (Fin m))) : List Bool := encode [setBits F,labels R,key.bits,labels H,labels G]

end MetricKMedianRecovery.BitMachine.BinaryJump

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
noncomputable def offset (x : List Bool) : List Bool :=
  (value (UnaryResources.lengthBits (extractPrefix (extractPrefix x)))*value (discardPrefix x)).bits
attribute [local irreducible] offset Drop.run
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_UnaryParser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.UnaryParser
open WordOperations UnaryTake

noncomputable def step_computes : PolyComputes step := by
  have ht:=pack_computes true ((const_computes [true]).append counter_computes)
    (data_computes.comp tail_computes) (const_computes [])
  have hf:=pack_computes false counter_computes (data_computes.comp tail_computes) (const_computes [])
  unfold step
  simpa only [Function.comp_def,List.singleton_append] using
    (data_computes.comp head_computes).cond ht hf
noncomputable def next_computes : PolyComputes next := by
  have h:=head_computes.cond step_computes id_computes
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [next,While.next,id_eq]
  cases x with
  | nil=>rfl
  | cons b xs=>cases b <;> rfl
lemma iterate_bounds (x : List Bool) (n : ℕ) :
    mass (next^[n] x)≤ mass x ∧ (next^[n] x).length≤ max x.length (2*mass x+3) := by
  induction n with
  | zero=>exact ⟨le_rfl,Nat.le_max_left _ _⟩
  | succ n ih=>
    rw [Function.iterate_succ_apply']
    have hm:=mass_next (next^[n] x)
    have hl:=length_next (next^[n] x)
    exact ⟨hm.trans ih.1,by omega⟩
end MetricKMedianRecovery.BitMachine.UnaryParser

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_FinSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMaskParser
open WordOperations WordList
noncomputable def run (x : List Bool) : List Bool :=
  BinaryNatSet.sort (filterWith member (pairBits (x,BinaryEllipsoidInitial.indices (RawUnary.run x))))
end MetricKMedianRecovery.BitMachine.BinaryMaskParser

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FinImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryTaggedSets
open WordOperations WordList BinaryArithmetic
variable {n : ℕ}
noncomputable def shift : List Bool→List Bool := BinaryNatSet.sort ∘ mapWith plus
noncomputable def unshift : List Bool→List Bool := BinaryNatSet.sort ∘ mapWith minus
end MetricKMedianRecovery.BitMachine.BinaryTaggedSets

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
open BinaryOpeningPayment (field field_encode)
attribute [local irreducible] WordList.mapWith
noncomputable def count (x : List Bool) : List Bool :=
  UnaryResources.lengthBits (Count.run (filterWith near x))
noncomputable def candidate (x : List Bool) : ℚ :=
  max (BinaryRational.decode (discardPrefix x))
    (BinaryRational.decode (field 0 (extractPrefix x)) /
      ((value (field 1 (extractPrefix x)):ℚ)*value (count (pairBits (discardPrefix x,field 2 (extractPrefix x))))))
noncomputable def candidates (x : List Bool) : List Bool :=
  mapWith (fun z=>BinaryRational.encode (candidate z)) (pairBits (x,field 2 x))
noncomputable def run (x : List Bool) : List Bool := RationalMin.run (candidates x)
end MetricKMedianRecovery.BitMachine.BinaryPopulation

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MenuMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMenu
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
noncomputable def index (x : List Bool) : List Bool := UnaryResources.lengthBits (exponent x)
attribute [local irreducible] UnaryResources.lengthBits
noncomputable def uniformRadius (x : List Bool) : ℚ :=
  (value (index x)+1)*BinaryRational.decode (field 0 (extractPrefix x))*BinaryRational.decode (field 1 (extractPrefix x))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryMenu

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
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
noncomputable def remove (x : List Bool) : List Bool := pairBits
  (BinaryNatSet.union (pairBits (extractPrefix (extractPrefix x),WordList.encode [discardPrefix x])),discardPrefix (extractPrefix x))
noncomputable def keep (x : List Bool) : Bool := decide
  (value (UnaryResources.lengthBits (Count.run (discardPrefix (discardPrefix x))))≤value (extractPrefix x) ∧
   value (UnaryResources.lengthBits (Count.run (extractPrefix (discardPrefix x))))≤value (extractPrefix x))
noncomputable def retain (x : List Bool) : List Bool := if keep x then WordList.encode [discardPrefix x] else []
end MetricKMedianRecovery.BitMachine.BinarySamplingState

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricArrays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricArrays
open WordOperations WordList
open BinaryOpeningPayment (field field_encode)
variable {n p q : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (rows : Fin p→Fin n) (cols : Fin q→Fin n) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.table rows,BinaryFinSet.table cols]
attribute [local irreducible] BinaryIndexMap.run
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryMetricArrays

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricCost2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricCost
open WordOperations WordList
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.encode D,BinaryFinSet.encode S]
end MetricKMedianRecovery.BitMachine.BinaryMetricCost

namespace MetricKMedianRecovery.BitMachine.BinaryMetricBest
open WordOperations WordList
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
def context (δ : Fin n→Fin n→ℚ) (D : Finset (Fin n)) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.encode D]
end MetricKMedianRecovery.BitMachine.BinaryMetricBest

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
open BinaryOpeningPayment (field field_encode)
def pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ) : List Bool :=
  encode [RationalMatrix.encode δ,List.replicate n true,BinaryFinSet.encode D,BinaryFinSet.encode F,
    BinaryFinSet.encode S,Δ.bits,BinaryRational.encode P,m.bits]
attribute [local irreducible] bound
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
open BinaryOpeningPayment (field field_encode)
attribute [local irreducible] src extra completeRaw BinaryRational.natWords
attribute [local irreducible] mapWith
def pack {n b : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (extra : List Bool) (seed : Fin (2*m)→Fin b→Bool) (complete : List Bool) : List Bool :=
  pairBits (BinarySampler.Parameters.pack δ D F S Δ P m,
    pairBits (extra,pairBits (BinarySeed.raw (ds:=[2*m]) seed,complete)))
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

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
open BinaryOpeningPayment (field field_encode)
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
def pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (g bits : List Bool) : List Bool := pairBits (BinarySampler.Parameters.pack δ D F S Δ P m,pairBits (g,bits))
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
attribute [local irreducible] extra Fair.raw RawUnary.run BinaryIntegralRecovery.result BinaryFinSet.encode BinarySampler.Parameters.pack BinaryMetricBest.best Fair.output List.ofFn BinarySeed.raw
attribute [local irreducible] mapWith
variable {n : ℕ}
noncomputable def output (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (hm : m≤n) (r0 y0 : Fin n) (t : ℕ) (seed : Fin t→Fin (Fair.count D Δ m)→Bool) : Finset (Fin n) :=
  BinaryMetricBest.best δ D S (List.ofFn (fun i=>Fair.output δ D F S Δ P m hm r0 y0 (seed i)))
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat

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
open BinaryOpeningPayment (field field_encode)
attribute [local irreducible] BinaryFinSet.encode Count.run src
attribute [local irreducible] mapWith
noncomputable def sizeWord (x : List Bool) : List Bool := UnaryResources.lengthBits (Count.run (src 4 x))
attribute [local irreducible] sizeWord
variable {n : ℕ}
abbrev pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (g raw : List Bool) : List Bool :=
  Fair.pack δ D F S Δ 0 0 g raw
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
open BinaryOpeningPayment (field field_encode)
attribute [local irreducible] BinaryLabelMatrix.row
def ctxBits {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Label (Fin m)))
    (R H G : List (Label (Fin m))) : List Bool :=
  encode [setBits F,labels R,labels H,labels G,pairBits (Rectangular.encode distance,List.replicate d true)]
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
open BinaryOpeningPayment (field field_encode)

def ctxBits {m : ℕ} (base : List Bool) (n q key : ℕ) (root : Label (Fin m)) (b : ℚ)
    (T U : List (List (Label (Fin m)))) : List Bool :=
  encode [base,List.replicate n true,List.replicate q true,key.bits,BinaryLabel.encode root,BinaryRational.encode b,
    historyBits T,historyBits U]
end MetricKMedianRecovery.BitMachine.BinaryLengthQuery

namespace MetricKMedianRecovery.BitMachine.BinaryLengthSearch
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_encode)
def resultBits {m : ℕ} : CanonicalLengthSearch.Result (Label (Fin m))→List Bool
  | .success s T=>encode [(0:ℕ).bits,BinaryRational.encode s,[],historyBits T,[]]
  | .bracket l u T U=>encode [(1:ℕ).bits,BinaryRational.encode l,BinaryRational.encode u,historyBits T,historyBits U]
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
open BinaryOpeningPayment (field field_encode)
def pack {m : ℕ} (base : List Bool) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (H : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) (J : Plan (Label (Fin m))) : List Bool :=
  encode [base,List.replicate n true,List.replicate q true,key.bits,BinaryRational.encode b,k.bits,List.replicate N true,
    labels H,historyBits T,historyBits U,BinaryLength.planBits J]
end MetricKMedianRecovery.BitMachine.BinarySensitive

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalCost
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_encode)
def pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (S : Finset (Label (Fin m))) : List Bool :=
  encode [Rectangular.encode distance,List.replicate d true,setBits S]
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
open BinaryOpeningPayment (field field_encode)
def pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Label (Fin m))) (S : Finset (Label (Fin m))) : List Bool :=
  encode [Rectangular.encode distance,List.replicate d true,labels fs,setBits S]
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
open BinaryOpeningPayment (field field_encode)
attribute [local irreducible] BinaryLabel.sort
def pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Fin m)) (r : ℕ) : List Bool :=
  encode [Rectangular.encode distance,List.replicate d true,labels (fs.map original),r.bits]
end MetricKMedianRecovery.BitMachine.BinaryLocalAnchor

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricAnchor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricAnchor
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field field_encode)
attribute [local irreducible] BinaryMetricArrays.run
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (r : ℕ) : List Bool :=
  encode [RationalMatrix.encode δ,List.replicate n true,BinaryFinSet.encode D,BinaryFinSet.encode F,r.bits]
attribute [local irreducible] WordList.map
attribute [local semireducible] WordList.map
end MetricKMedianRecovery.BitMachine.BinaryMetricAnchor

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
open BinaryOpeningPayment (field field_encode)
namespace R
abbrev pack := @BinaryIntegralRecovery.Guesses.pack
end R
attribute [local irreducible] UnaryResources.lengthBits
attribute [local irreducible] mapWith
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
def pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Fin m)) (S : Finset (Fin m)) : List Bool :=
  BinaryLocalSearch.pack distance (fs.map original) (S.image original)
end MetricKMedianRecovery.BitMachine.BinaryLocalRefine

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
open BinaryOpeningPayment (field field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

def pack {m : ℕ} (sensitive : List Bool) (B : Finset (Label (Fin m))) (P : List (List (Label (Fin m))))
    (R : CanonicalLengthSearch.Result (Label (Fin m))) : List Bool := encode [sensitive,setBits B,historyBits P,BinaryLengthSearch.resultBits R]
end MetricKMedianRecovery.BitMachine.BinaryPlanResult

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ResolveMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryResolve
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge CanonicalLengthView
open BinaryOpeningPayment (field field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
def pack {m : ℕ} (base : List Bool) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (B : Finset (Label (Fin m))) (P : List (List (Label (Fin m)))) (R : CanonicalMergeCrossing.Result (Label (Fin m))) : List Bool :=
  encode [base,List.replicate n true,List.replicate q true,key.bits,BinaryRational.encode b,k.bits,List.replicate N true,
    setBits B,historyBits P,BinaryCross.resultBits R]
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
open BinaryOpeningPayment (field field_encode)

def accBits {m : ℕ} (s : Acc (Label (Fin m))) : List Bool :=
  encode [labels s.front,labels s.rest,historyBits s.vertices]
attribute [local irreducible] BinaryLabel.copied
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

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FirstPresent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNodeScan
open WordOperations WordList RationalLeaves CanonicalMergeRefinement CanonicalMergeCrossing
open BinaryCross (ctxBits nodeBits resultBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_encode)
def pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ) (U : List (List (Label (Fin m))))
    (nodes : List (List (Label (Fin m)) × List (List (Label (Fin m))))) : List Bool :=
  encode [ctxBits F Q k,historyBits U,encode (nodes.map nodeBits)]
end MetricKMedianRecovery.BitMachine.BinaryNodeScan

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
open BinaryOpeningPayment (field field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outputBits)
def output {m : ℕ} : StartOutput (Fin m)→List Bool
  | .small o=>pairBits ([],outputBits o)
  | .normal o=>pairBits ([true],outputBits o)

end MetricKMedianRecovery.BitMachine.BinaryInitial

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
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (Δ h L : ℕ) : List Bool :=
  encode [RationalMatrix.encode δ,List.replicate n true,BinaryFinSet.encode D,BinaryFinSet.encode F,Δ.bits,h.bits,L.bits]
end MetricKMedianRecovery.BitMachine.BinaryMetricSurplus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_RoundingMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
noncomputable def rowIndex_computes : PolyComputes rowIndex := extractPrefix_computes.comp discardPrefix_computes
end MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_NormalizationMachine
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNormalization
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
open IntegralAssembly (gammaRat)
def pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (d : ℕ) (M : ℚ) : List Bool :=
  encode [RationalMatrix.encode δ,List.replicate n true,List.replicate d true,BinaryRational.encode M]
noncomputable def count (x : List Bool) : List Bool := UnaryResources.lengthBits (field 2 x)
noncomputable def mesh (x : List Bool) : List Bool := BinaryRational.encode
  ((gammaRat/16)*BinaryRational.decode (field 3 x)/(value (count x):ℚ))
noncomputable def capArgument (x : List Bool) : List Bool := BinaryRational.encode
  (20*(value (count x):ℚ)*(value (count x):ℚ)/(gammaRat/16))
noncomputable def cap (x : List Bool) : List Bool :=
  (⌈BinaryRational.decode (capArgument x)⌉₊+1).bits
noncomputable def roundingInput (x : List Bool) : List Bool :=
  encode [BinaryDuplicateMatrix.run (field 0 x),BinaryDuplicateMatrix.twice (field 1 x),mesh x,cap x]
noncomputable def run : List Bool→List Bool := BinaryRoundingMatrix.run ∘ roundingInput
end MetricKMedianRecovery.BitMachine.BinaryNormalization

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalCall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalZero
open WordOperations WordList
open BinaryRationalSort (entryBits)
variable {n : ℕ}
noncomputable def rowRun (x : List Bool) : List Bool :=
  discardPrefix (BinaryRationalMinKey.run (mapWith BinarySamplingReference.original x))
end MetricKMedianRecovery.BitMachine.BinaryGlobalZero

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalZero
open WordOperations WordList LocalSearch
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) : List Bool :=
  BinaryMetricArrays.pack δ (SortedIndex.enum D) (SortedIndex.enum F)
noncomputable def one (x : List Bool) : List Bool :=
  rowRun (pairBits (BinaryMetricArrays.row x,field 2 (extractPrefix x)))
noncomputable def values (x : List Bool) : List Bool := mapWith one (pairBits (x,field 1 x))
noncomputable def run : List Bool→List Bool := BinaryNatSet.sort ∘ values
end MetricKMedianRecovery.BitMachine.BinaryGlobalZero

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
open BinaryOpeningPayment (field field_encode)
noncomputable def scales : List Bool→List Bool := BinaryInputParser.Stream.run ∘ BinaryInputParser.Metric.rawMatrix
attribute [local irreducible] BinaryInputParser.Metric.budget
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end


