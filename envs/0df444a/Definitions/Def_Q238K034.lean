-- Prove2me | Definitions.Def_Q238K034
-- name    : Q238K034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:27:29.316756+00:00
-- url     : https://prove2.me/theorems/2928303e-0718-43b2-b105-5a8474f00e63
-- title:
--   Definitions bundle Q238K034 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 103 declarations of OpenAI's Lean: 103 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.blog`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.craw`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.lraw`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.lshape`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.lsize`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.tailBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.cut`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.leftShape`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.lword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.tword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.cut`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.leftShape`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.lword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.tword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.lword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.tword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.unary`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.context_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.drawRow_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.elementPart_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.elementSamples_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.initial_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.stepScore_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.look_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.offers_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.a`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.directed`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.finalCount`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.forward`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.leftCount`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.leftLength`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.leftPaid`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.mixedCount`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.paid`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.rightCount`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.rightLength`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.rightPaid`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.sandwiched` and 63 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_IntegralRecoveryAmplified`, `KMedianRecovery_Algorithms_IntegralRecoveryDemand`, `KMedianRecovery_Algorithms_IntegralRecoveryGuesses`, `KMedianRecovery_Algorithms_IntegralRecoveryMachine`, `KMedianRecovery_Algorithms_IntegralRecoveryRepeat`, `KMedianRecovery_Algorithms_IntegralRecoverySelection`, `KMedianRecovery_Algorithms_IntegralRecoverySuccess`, `KMedianRecovery_Branching_BranchSeedLayout`, `KMedianRecovery_Branching_CategoricalChoice`, `KMedianRecovery_Branching_CategoricalOutput`, `KMedianRecovery_Branching_CategoricalRawPrep`, `KMedianRecovery_Branching_CategoricalScore`, `KMedianRecovery_Branching_CategoricalSize`, `KMedianRecovery_Branching_CategoricalTable`, `KMedianRecovery_Branching_ObservableCapacity`, `KMedianRecovery_Branching_PopulationMachine`, `KMedianRecovery_Branching_RandomizedZeroBranch`, `KMedianRecovery_Encoding_BoundedNatWord`, `KMedianRecovery_Encoding_RationalCap`, `KMedianRecovery_Geometry_LocalSets`, `KMedianRecovery_Geometry_RoundingArithmetic`, `KMedianRecovery_Machines_RefineMachine`, `KMedianRecovery_Machines_SliceFold`, `KMedianRecovery_Machines_StepMachine`, `KMedianRecovery_Recovery_Answer`, `KMedianRecovery_Recovery_CrossCount`, `KMedianRecovery_Recovery_CrossEdge`, `KMedianRecovery_Recovery_FinishPhase`, `KMedianRecovery_Recovery_FirstPresent`, `KMedianRecovery_Recovery_OrientedSearch`, `KMedianRecovery_Recovery_RecoveryContext`, `KMedianRecovery_Recovery_RefineMath`, `KMedianRecovery_Sampling_SamplerDraw`, `KMedianRecovery_Sampling_SamplerParameters`, `KMedianRecovery_Sampling_SamplerWeights`, `KMedianRecovery_Strictness_SurplusPostprocess`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K028`, `Q238K029` and `Q238K030` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K037` and `Q238K038`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.cut_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.a_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.finalCount_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.demandWord_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Fair_output_exponential_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.repack_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.ranges_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape.demandWord_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.recoveryContext_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.sampleContext_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.view_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNodeScan.markers_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryRecovery_positiveSeed_probability_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRefine.cutOp_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Update_chosen_pair_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Update_old_pair_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_oracle_pair_s238`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.cut_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.a_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.finalCount_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.demandWord_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Fair_output_exponential_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.repack_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.ranges_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape.demandWord_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.recoveryContext_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.sampleContext_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.view_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNodeScan.markers_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryRecovery_positiveSeed_probability_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRefine.cutOp_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Update_chosen_pair_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Update_old_pair_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_oracle_pair_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K028
import Definitions.Def_Q238K029
import Definitions.Def_Q238K030

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
variable {E : Type*} {a T : ℕ}
noncomputable def drawRow_computes : PolyComputes drawRow :=
  ((discardPrefix_computes.comp extractPrefix_computes).pair
    (extractPrefix_computes.comp (field_computes 0))).comp Lookup.run_computes
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
open BinaryOpeningPayment (field field_computes )
variable {q a T L : ℕ}
noncomputable def elementPart_computes : PolyComputes elementPart :=
  (discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 3))).comp Lookup.run_computes
noncomputable def elementSamples_computes : PolyComputes elementSamples :=
  (discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 2))).comp Lookup.run_computes
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryCategorical

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
open BinaryOpeningPayment (field field_computes )
variable {q a T L : ℕ}
noncomputable def stepScore_computes : PolyComputes stepScore :=
  cons_computes (Find.context_computes.comp (field_computes 0))
    (cons_computes (Fold.accum_computes.comp (field_computes 1))
      (cons_computes Find.item_computes (cons_computes (Find.context_computes.comp (field_computes 1)) (const_computes []))))
attribute [local irreducible] advance choices
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
variable {q a T L : ℕ}
noncomputable def initial_computes : PolyComputes initial := by
  have computation := cons_computes (const_computes []) (cons_computes
    (((field_computes 2).pair (((field_computes 3).pair (const_computes [])).comp repeatWords_computes)).comp repeatWords_computes)
    (const_computes []))
  unfold initial
  simpa only [Function.comp_def, encode] using computation
noncomputable def context_computes : PolyComputes context :=
  cons_computes (field_computes 0) (cons_computes (field_computes 1) (cons_computes (field_computes 3) (const_computes [])))
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Answer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFinish
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
noncomputable def step (x : List Bool) : List Bool :=
  if answer x=[] then x else BinaryPhaseUpdate.run (pairBits (x,(answer x).tail))
end MetricKMedianRecovery.BitMachine.BinaryPhaseFinish

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
  WordList.Fold.run
noncomputable def powerInput_computes : PolyComputes powerInput :=
  (list_computes [(fun _=>[]),(fun _=>[]),id,(fun _=>BinaryRational.encode 1),
    (fun _=>BinaryRational.encode 0),(fun _=>BinaryRational.encode 0),(fun _=>[]),(fun _=>[]),(fun _=>[])] (by
      intro f hf
      refine Classical.choice ?_
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
      rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals first | exact ⟨id_computes⟩ | exact ⟨const_computes _⟩)).pair (const_computes [])
end MetricKMedianRecovery.BitMachine.BinaryPhaseCount

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources
open WordOperations WordList BinaryArithmetic
open Categorical.Explicit

attribute [local irreducible] bword tbits RawTake.run RawUnary.run NaturalArray.exponentiate
attribute [local irreducible] qnext anext
attribute [local irreducible] factor
attribute [local irreducible] cap
noncomputable def unary (w : List Bool→List Bool) (x : List Bool) : List Bool := RawUnary.run (RawTake.run (pairBits (w x,cap.word x)))
noncomputable def tword := unary tbits
noncomputable def lword := unary lbits
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalRawPrep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
open Categorical.Explicit
variable {q a : ℕ}
noncomputable def tword (x : List Bool) : List Bool := Resources.tword (dimensions x)
noncomputable def lword (x : List Bool) : List Bool := Resources.lword (dimensions x)
attribute [local irreducible] Resources.tword Resources.lword Resources.bword dimensions
noncomputable def leftShape (x : List Bool) : List Bool := encode [tword x,qword x,lword x,aword x,bword x]
noncomputable def cut (x : List Bool) : List Bool := BinarySeed.product 5 (leftShape x)
attribute [local irreducible] BinarySeed.product leftShape
attribute [local irreducible] RawTake.run RawDrop.run cut rightShape tword lword bword
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare

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
open BinaryOpeningPayment (field field_computes )
attribute [local irreducible] WordList.mapWith
noncomputable def run (x : List Bool) : List Bool := RationalMin.run (candidates x)
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
open BinaryOpeningPayment (field field_computes )

noncomputable def look_computes : PolyComputes look :=
  (discardPrefix_computes.pair extractPrefix_computes).comp Lookup.run_computes
attribute [local irreducible] mapWith
noncomputable def offers_computes : PolyComputes offers := by
  unfold offers
  exact ((discardPrefix_computes.comp (field_computes 1)).pair extractPrefix_computes).comp (mapWith_computes look_computes)
attribute [local irreducible] RationalMin.run
end MetricKMedianRecovery.BitMachine.BinaryCompletion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Client
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
attribute [local irreducible] BinarySamplingOracle.row BinaryIndexMap.run
variable {n : ℕ}
noncomputable def distances (x : List Bool) : List Bool := BinaryIndexMap.run (pairBits (row x,c 2 (extractPrefix x)))
noncomputable def population (x : List Bool) : List Bool := BinaryPopulation.run (encode [c 6 (extractPrefix x),c 8 (extractPrefix x),distances x])
end MetricKMedianRecovery.BitMachine.BinarySampler.Client

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
open BinaryOpeningPayment (field field_computes )
attribute [local irreducible] Count.run BinaryBisection.logWord RawTake.run RawDrop.run
noncomputable def blog (x : List Bool) : List Bool := BinaryBisection.logWord (lengthBits (field 8 x))
noncomputable def lshape (x : List Bool) : List Bool := encode [nword x,blog x]
noncomputable def lsize (x : List Bool) : List Bool :=
  (value (UnaryResources.lengthBits (nword x))*value (UnaryResources.lengthBits (blog x))).bits
noncomputable def craw (x : List Bool) : List Bool := RawTake.run (pairBits (csize (extractPrefix x),discardPrefix x))
noncomputable def lraw (x : List Bool) : List Bool := RawTake.run (pairBits (lsize (extractPrefix x),rest x))
noncomputable def tailBits (x : List Bool) : List Bool := RawDrop.run (pairBits (lsize (extractPrefix x),rest x))
end MetricKMedianRecovery.BitMachine.BinaryBranchRandomize

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
open BinaryOpeningPayment (field field_computes )
variable {n : ℕ}
noncomputable def rhs (x : List Bool) : List Bool :=
  (value (lengthBits (extractPrefix (field 5 x)))+value (field 9 x)).bits
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

namespace MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count
open WordOperations WordList BinaryArithmetic BinaryBranchContext
open BinaryOpeningPayment (field field_computes )
open BinaryCategorical
attribute [local irreducible] dimensions Resources.tword Resources.lword Resources.bword BinarySeed.product
noncomputable def tword (x : List Bool) : List Bool := Resources.tword (dimensions x)
noncomputable def lword (x : List Bool) : List Bool := Resources.lword (dimensions x)
noncomputable def leftShape (x : List Bool) : List Bool := encode [tword x,qword x,lword x,pword x,bword x]
attribute [local irreducible] leftShape rightShape BinaryBranchRandomize.csize BinaryBranchRandomize.lsize
noncomputable def run (x : List Bool) : List Bool :=
  (value (BinaryBranchRandomize.csize x)+value (BinaryBranchRandomize.lsize x)+
    (value (BinarySeed.product 5 (leftShape x))+value (BinarySeed.product 2 (rightShape x)))).bits
noncomputable def cut (x : List Bool) : List Bool := pairBits (extractPrefix x,
  RawTake.run (pairBits (run (extractPrefix x),discardPrefix x)))
attribute [local irreducible] run RawTake.run
end MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RecoveryContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
noncomputable def cword (x : List Bool) : List Bool := RawTake.run (pairBits (cbits x,src 6 x))
noncomputable def bword (x : List Bool) : List Bool := RawTake.run (pairBits (bbits x,src 7 x))
attribute [local irreducible] RawTake.run BinaryEllipsoidInitial.indices
attribute [local irreducible] mapWith
noncomputable def labels (x : List Bool) : List Bool := BinaryEllipsoidInitial.indices (bword x)
noncomputable def context (x : List Bool) : List Bool :=
  encode [src 0 x,src 1 x,src 2 x,src 3 x,src 4 x,src 5 x,zeros x,zeros x,labels x,qbits x,cword x,src 8 x]
attribute [local irreducible] src zeros labels qbits cword bword
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_BoundedNatWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BoundedNatWord
open WordOperations
noncomputable def run (P : Polynomial ℕ) (x : List Bool) : List Bool :=
  RawUnary.run (RawTake.run (pairBits (extractPrefix x,(counter P).word (discardPrefix x))))
attribute [local irreducible] RawTake.run RawUnary.run counter
end MetricKMedianRecovery.BitMachine.BoundedNatWord

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
open BinaryOpeningPayment (field field_computes )
noncomputable def unary (j : ℕ) (x : List Bool) : List Bool := BoundedNatWord.run bound (pairBits (field j x,x))
attribute [local irreducible] BoundedNatWord.run bound
noncomputable def Jword (x : List Bool) : List Bool := [true]++RepeatedAppend.copies (unary 7 x).length (List.replicate 2000000 true)
noncomputable def precision (x : List Bool) : List Bool :=
  nword x++unary 5 x++List.replicate M true++List.replicate E true++Jword x++List.replicate 5 true
noncomputable def menus (x : List Bool) : List Bool := encode [List.replicate M true,List.replicate E true,Jword x]
noncomputable def run (x : List Bool) : List Bool := encode [dimension x,field 0 x,field 2 x,field 3 x,field 4 x,
  diameter x,field 6 x,BinaryRational.encode (1/1000000),field 7 x,menus x]
end MetricKMedianRecovery.BitMachine.BinarySampler.Parameters

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
open BinaryOpeningPayment (field field_computes )
variable {n : ℕ}
noncomputable def actions (x : List Bool) : List Bool := BinaryActions.run (pairBits (c 2 (input x),c 9 (input x)))
noncomputable def weights (x : List Bool) : List Bool := mapWith (fun y=>BinaryRational.encode (Weights.weight y))
  (pairBits (Weights.context (input x),actions x))
end MetricKMedianRecovery.BitMachine.BinarySampler.Draw

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
open BinaryOpeningPayment (field field_computes )
noncomputable def mword : List Bool→List Bool := BinarySampler.Parameters.unary 7 ∘ params
noncomputable def cfg : List Bool→List Bool := BinarySampler.Parameters.run ∘ params
noncomputable def precision : List Bool→List Bool := BinarySampler.Parameters.precision ∘ params
noncomputable def sampleContext (x : List Bool) : List Bool :=
  encode [cfg x,mword x,mword x++mword x,precision x,sampleRaw x]
noncomputable def recoveryContext (x : List Bool) : List Bool :=
  encode [src 0 x,src 2 x,src 3 x,src 4 x,BinaryRational.natWords (src 5 x),pairBits ([],[]),src 1 x,mword x,extra x,completeRaw x]
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
noncomputable def sampleCount (x : List Bool) : List Bool :=
  (2*(mword x).length*(precision x).length).bits
noncomputable def repack (x : List Bool) : List Bool := pairBits (extractPrefix x,
  pairBits (extra x,pairBits (RawTake.run (pairBits (sampleCount x,raw x)),RawDrop.run (pairBits (sampleCount x,raw x)))))
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
open BinaryOpeningPayment (field field_computes )
noncomputable def sampleWord (x : List Bool) : List Bool := RepeatedAppend.copies (mword x++mword x).length (precision x)
noncomputable def demandWord (x : List Bool) : List Bool := sampleWord x++completionWord x
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
noncomputable def bword : List Bool→List Bool := RawUnary.run ∘ Fair.demandWord
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
noncomputable def demandWord (Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  RepeatedAppend.copies (Repeat.rword Q x).length (Repeat.bword x)
noncomputable def demandBits (Q : Polynomial ℕ) : List Bool→List Bool := UnaryResources.lengthBits ∘ demandWord Q
attribute [local irreducible] demandBits
noncomputable def cut (Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  pairBits (extractPrefix x,pairBits (extra x,RawTake.run (pairBits (demandBits Q x,Fair.raw x))))
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
open BinaryOpeningPayment (field field_computes )
attribute [local irreducible] BinaryFinSet.encode BinarySampler.Parameters.unary Count.run src
noncomputable def costWord (x : List Bool) : List Bool := RepeatedAppend.copies (Count.run (src 2 x)).length
  (BinarySampler.Parameters.unary 5 (extractPrefix x))
noncomputable def costRange (x : List Bool) : List Bool := BinaryEllipsoidInitial.indices (costWord x++[true])
noncomputable def choices (x : List Bool) : List Bool := cross (pairBits (costRange x,countRange x))
attribute [local irreducible] mapWith
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
noncomputable def atDemand (Q : Polynomial ℕ) : List Bool→List Bool := Repeat.FiniteTape.demandWord Q ∘ atInput
noncomputable def demandWords (Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  mapWith (atDemand Q) (pairBits (x,choices x))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

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
open BinaryOpeningPayment (field field_computes )
noncomputable def size_computes : PolyComputes size := Count.run_computes.comp UnaryResources.lengthBits_computes
end MetricKMedianRecovery.BitMachine.BinaryLocalSets

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_RoundingArithmetic
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace NatOps
noncomputable def max {f g : List Bool→List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>(Max.max (value (f x)) (value (g x))).bits) := by
  have hh:=(le hf hg).cond (hg.comp normalize_computes) (hf.comp normalize_computes)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [decide_eq_true_eq,Function.comp_def,normalize_eq_bits]
  split_ifs with h
  · rw [max_eq_right h]
  · rw [max_eq_left (le_of_not_ge h)]
end NatOps
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SliceFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Slices
open WordOperations CanonicalSlices
open BinaryOpeningPayment (field field_computes )

noncomputable def sf_computes (n : ℕ) : PolyComputes (sf n) :=
  (discardPrefix_computes.comp discardPrefix_computes).comp (field_computes n)
noncomputable def front_computes : PolyComputes front := (sf_computes 0).append (cons_computes item_computes (const_computes []))
noncomputable def rest_computes : PolyComputes rest := (sf_computes 1).comp tail_computes
noncomputable def cut_computes : PolyComputes cut := list_computes [sf 0,item,rest] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨sf_computes _⟩
  · exact ⟨item_computes⟩
  · exact ⟨rest_computes⟩)
noncomputable def output_computes : PolyComputes output := (sf_computes 2).append (cons_computes cut_computes (const_computes []))
noncomputable def step_computes : PolyComputes step := list_computes [front,rest,output] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨front_computes⟩
  · exact ⟨rest_computes⟩
  · exact ⟨output_computes⟩)
noncomputable def initial_computes : PolyComputes initial := Fold.pack_computes id_computes (const_computes [])
  (list_computes [fun _=>[],id,fun _=>[]] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨const_computes []⟩
    · exact ⟨id_computes⟩
    · exact ⟨const_computes []⟩))
end MetricKMedianRecovery.BitMachine.WordList.Slices

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CrossCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCross
open WordOperations WordList RationalLeaves BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes )

noncomputable def paid (x : List Bool) : List Bool := BinaryFiniteContext.countInter (pairBits (opened x,cf 0 x))
noncomputable def finalCount (x : List Bool) : List Bool := BinaryFiniteContext.countInter (pairBits (finalOpened x,cf 0 x))
end MetricKMedianRecovery.BitMachine.BinaryCross

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes )
noncomputable def removedTail (x : List Bool) : List Bool :=
  Drop.run (pairBits ((value (lengthBits (field 3 x))-1).bits,field 4 x))
attribute [local irreducible] removedTail
noncomputable def removeOp (x : List Bool) : List Bool :=
  encode [(1:ℕ).bits,jf 0 x,jf 2 x,removedTail (extractPrefix x),jf 1 x]
noncomputable def removes (x : List Bool) : List Bool := mapWith removeOp (pairBits (x,Slices.run (field 3 x)))
noncomputable def candidates (x : List Bool) : List Bool := (adds x++removes x)++replaces x
noncomputable def view (x : List Bool) : List Bool := Find.run accepts (pairBits (x,candidates x))
end MetricKMedianRecovery.BitMachine.BinaryJump

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
open BinaryOpeningPayment (field field_computes )
noncomputable def edgeView : List Bool → List Bool := view ∘ field 0
noncomputable def edge (x : List Bool) : List Bool :=
  if edgeView x=[] then cons (edgeG x) [] else expand (pairBits (edgeData x,(edgeView x).tail))
end MetricKMedianRecovery.BitMachine.BinaryJump

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_RefineMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRefine
open WordOperations WordList RationalLeaves CanonicalMergeRefinement
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes )
noncomputable def cutOp (x : List Bool) : List Bool := if cutTail x=[] then [] else BinaryJump.edge (edgeInput x)
noncomputable def run : List Bool → List Bool := flatMapWith cutOp ∘ runInput
end MetricKMedianRecovery.BitMachine.BinaryRefine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CrossEdge
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCross
open WordOperations WordList RationalLeaves BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes )
attribute [local irreducible] paid finalCount

noncomputable def leftPaid : List Bool → List Bool := paid ∘ leftData
noncomputable def rightPaid : List Bool → List Bool := paid ∘ rightData
noncomputable def leftLength : List Bool → List Bool := lengthBits ∘ extractPrefix ∘ leftNode
noncomputable def rightLength : List Bool → List Bool := lengthBits ∘ extractPrefix ∘ rightNode
noncomputable def forward (x : List Bool) : Bool :=
  if decide (value (leftPaid x)=value (rightPaid x)) then decide (value (leftLength x)<value (rightLength x))
  else decide (value (rightPaid x)<value (leftPaid x))
noncomputable def mixedCount (x : List Bool) : List Bool := finalCount (pairBits (extractPrefix x,mixed x))
noncomputable def directed (x : List Bool) : List Bool :=
  if decide (value (leftLength x)=value (rightLength x)) then
    if decide (value (mixedCount x)=value (cf 2 x)) then successNode (mixed x) else mixedCommon x
  else taggedPair 2 (discardPrefix x)
noncomputable def edge (x : List Bool) : List Bool := if forward x then directed x else directed (flipped x)
end MetricKMedianRecovery.BitMachine.BinaryCross

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_OrientedSearch
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryOrientedSearch
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
noncomputable def reverseContext_computes : PolyComputes reverseContext := (field_computes 1).pair (field_computes 4)
noncomputable def reverseInput_computes : PolyComputes reverseInput :=
  list_computes [field 0,reverseContext,field 2,field 3,field 4] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨field_computes _⟩ | exact ⟨reverseContext_computes⟩)
noncomputable def reverseRun (query : List Bool→List Bool) (x : List Bool) : List Bool :=
  reflect (pairBits (field 4 x,BinaryBisection.run (reversed query) (reverseInput x)))
noncomputable def run (query : List Bool→List Bool) (x : List Bool) : List Bool :=
  if isReversed query x then reverseRun query x else BinaryBisection.run query x
end MetricKMedianRecovery.BitMachine.BinaryOrientedSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FirstPresent
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCross
open WordOperations WordList RationalLeaves BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes )
attribute [local irreducible] finalCount paid edge
noncomputable def leftCount : List Bool → List Bool := finalCount ∘ leftData
noncomputable def rightCount : List Bool → List Bool := finalCount ∘ rightData
noncomputable def sandwiched (x : List Bool) : Bool :=
  (decide (value (leftCount x)<value (cf 2 x)) && decide (value (cf 2 x)<value (rightCount x))) ||
  (decide (value (rightCount x)<value (cf 2 x)) && decide (value (cf 2 x)<value (leftCount x)))
noncomputable def transition (x : List Bool) : List Bool :=
  if decide (value (rightCount x)=value (cf 2 x)) then true::successNode (rightNode x)
  else if sandwiched x then true::edge x else []
end MetricKMedianRecovery.BitMachine.BinaryCross

namespace MetricKMedianRecovery.BitMachine.BinaryNodeScan
open WordOperations WordList RationalLeaves CanonicalMergeRefinement CanonicalMergeCrossing
open BinaryCross (ctxBits nodeBits resultBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes )
attribute [local irreducible] BinaryCross.transition
noncomputable def cutOp (x : List Bool) : List Bool :=
  if suffix x=[] then [] else BinaryCross.transition (transitionInput x)
noncomputable def markers : List Bool → List Bool := mapWith cutOp ∘ scanInput
noncomputable def run (x : List Bool) : List Bool := FirstPresent.run (pairBits (fallback x,markers x))
end MetricKMedianRecovery.BitMachine.BinaryNodeScan

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
open BinaryOpeningPayment (field field_computes )
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outcomeBits)
noncomputable def a (x : List Bool) : List Bool := BinaryFiniteContext.countInter (pairBits (BinaryFiniteMachine.after (pairBits (Q x,sf 5 x)),bf 2 x))
end MetricKMedianRecovery.BitMachine.BinaryCoupledStep

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_SurplusPostprocess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field field_computes )
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
noncomputable def target (x : List Bool) : List Bool :=
  (max (value (field 4 x)) (value (lengthBits (field 3 x)))).bits
end MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess

end OAI
end


