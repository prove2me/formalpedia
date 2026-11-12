-- Prove2me | Definitions.Def_Q238L034
-- name    : Q238L034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:31:58.909057+00:00
-- url     : https://prove2.me/theorems/773cd3a1-a0ea-4a57-ae9a-740ceb906078
-- title:
--   Definitions bundle Q238L034 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 108 declarations of OpenAI's Lean: 108 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.blog`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.colors`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.context`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.craw`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.labels`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.lraw`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.lshape`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.lsize`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.tailBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.cut`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.leftShape`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.lword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.tword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize.clip`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize.clipped`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize.keep`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize.output`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize.size`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.cut`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.left`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.leftShape`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.lword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.right`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.runInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.tword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.lword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.tword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.unary`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.context_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.drawRow_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.elementPart_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.elementSamples_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.initial_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.stepScore_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryColorLabel.colors`, `OAI.MetricKMedianRecovery.BitMachine.BinaryColorLabel.labels`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.look_computes` and 68 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_CandidateSanitize`, `KMedianRecovery_Branching_BranchSeedLayout`, `KMedianRecovery_Branching_CategoricalChoice`, `KMedianRecovery_Branching_CategoricalOutput`, `KMedianRecovery_Branching_CategoricalRawPrep`, `KMedianRecovery_Branching_CategoricalScore`, `KMedianRecovery_Branching_CategoricalSize`, `KMedianRecovery_Branching_CategoricalTable`, `KMedianRecovery_Branching_CompletionFair`, `KMedianRecovery_Branching_CompletionFillMath`, `KMedianRecovery_Branching_CompletionRealize`, `KMedianRecovery_Branching_RandomizedZeroBranch`, `KMedianRecovery_Branching_RationalSurrogate`, `KMedianRecovery_Encoding_BoundedNatWord`, `KMedianRecovery_Encoding_ColorLabelMachine`, `KMedianRecovery_Encoding_FinSetDecode`, `KMedianRecovery_Encoding_FinSets`, `KMedianRecovery_Encoding_RationalBottomIndices`, `KMedianRecovery_Encoding_RationalCap`, `KMedianRecovery_Encoding_RationalSort`, `KMedianRecovery_Encoding_WordTake`, `KMedianRecovery_Geometry_LocalSets`, `KMedianRecovery_Geometry_RoundingArithmetic`, `KMedianRecovery_Machines_RefineMachine`, `KMedianRecovery_Machines_SliceFold`, `KMedianRecovery_Machines_StepMachine`, `KMedianRecovery_Recovery_CrossCount`, `KMedianRecovery_Recovery_CrossEdge`, `KMedianRecovery_Recovery_FinishPhase`, `KMedianRecovery_Recovery_FirstPresent`, `KMedianRecovery_Recovery_OrientedSearch`, `KMedianRecovery_Recovery_RawUnary`, `KMedianRecovery_Recovery_RefineMath`, `KMedianRecovery_Sampling_InverseCDF`, `KMedianRecovery_Sampling_SeedTensor`, `KMedianRecovery_Strictness_SurplusPostprocess`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L027`, `Q238L028` and `Q238L029` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L037` and `Q238L038`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.context_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.labels_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.cut_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.left_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.redIndices_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.saving_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.a_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.finalCount_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.lookup_draw_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.pad_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.find_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.view_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.sumBottom_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRefine.cutOp_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySeed.nest_tensor_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.integral_spec_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.localInput_pack_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.context_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.labels_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.cut_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.left_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.redIndices_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.saving_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.a_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.finalCount_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.lookup_draw_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.pad_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.find_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.view_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.sumBottom_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRefine.cutOp_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySeed.nest_tensor_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.integral_spec_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.localInput_pack_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L027
import Definitions.Def_Q238L028
import Definitions.Def_Q238L029

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordTake
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Take
open WordOperations BinaryArithmetic
noncomputable def number (x : List Bool) : List Bool :=
  (value (lengthBits (discardPrefix x))-value (extractPrefix x)).bits
noncomputable def run (x : List Bool) : List Bool :=
  reverse (Drop.run (pairBits (number x,reverse (discardPrefix x))))
attribute [local irreducible] number reverse Drop.run
end MetricKMedianRecovery.BitMachine.WordList.Take

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalSort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordOperations WordList BinaryArithmetic

attribute [local irreducible] sort ranked Take.run
noncomputable def bottom (x : List Bool) : List Bool :=
  Take.run (pairBits (extractPrefix x,sort (ranked (discardPrefix x))))
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionFillMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionPad
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
noncomputable def need (x : List Bool) : List Bool := (value (field 2 x)-value (lengthBits (field 1 x))).bits
noncomputable def remaining (x : List Bool) : List Bool := BinaryNatSet.diff (pairBits (field 0 x,field 1 x))
noncomputable def run (x : List Bool) : List Bool := BinaryNatSet.union (pairBits (field 1 x,Take.run (pairBits (need x,remaining x))))
attribute [local irreducible] need remaining BinaryNatSet.union Take.run
end MetricKMedianRecovery.BitMachine.BinaryCompletionPad

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RawUnary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.RawUnary
open WordOperations
noncomputable def run_computes : PolyComputes run := by
  have hh:=UnaryResources.copy_computes id_computes (const_computes [true])
  unfold run
  simpa only [id_eq,copies_singleton] using hh
end MetricKMedianRecovery.BitMachine.RawUnary

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_FinSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordOperations WordList BinaryArithmetic

noncomputable def sumBottom (x : List Bool) : List Bool :=
  RationalArray.sumWords (mapWith (fun y=>extractPrefix (discardPrefix y)) (pairBits ([],bottom x)))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalBottomIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordOperations WordList BinaryArithmetic
noncomputable def rawIndices (x : List Bool) : List Bool :=
  mapWith (fun y=>discardPrefix (discardPrefix y)) (pairBits ([],bottom x))
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SeedTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
open WordOperations WordList BinaryArithmetic
noncomputable def chunk (d : ℕ) (x : List Bool) : List Bool := RawTake.run (pairBits (width d x,
  RawDrop.run (pairBits ((value (width d x)*value (discardPrefix x)).bits,discardPrefix (extractPrefix x)))))
attribute [local irreducible] width RawTake.run RawDrop.run
noncomputable def child (d : ℕ) (x : List Bool) : List Bool :=
  pairBits (tail (extractPrefix (extractPrefix x)),chunk d x)
noncomputable def nest : ℕ→List Bool→List Bool
  | 0,x =>normalizeBig (discardPrefix x)
  | d+1,x =>mapWith (fun y=>nest d (child d y)) (pairBits (x,indices x))
end MetricKMedianRecovery.BitMachine.BinarySeed

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
noncomputable def colors (x : List Bool) : List Bool :=
  mapWith (colorWord ∘ discardPrefix) (pairBits ([],BinarySeed.nest 1 x))
noncomputable def labels (x : List Bool) : List Bool :=
  mapWith labelOp (pairBits (extractPrefix x,BinarySeed.nest 1 (discardPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryColorLabel

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_InverseCDF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInverseCDF
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
open Dyadic.Canonical

noncomputable def prefixCounts (x : List Bool) : List Bool :=
  Take.run (pairBits (UnaryResources.inc (discardPrefix x),extractPrefix (extractPrefix x)))
attribute [local irreducible] Take.run UnaryResources.inc
noncomputable def total (x : List Bool) : List Bool := NaturalArray.sumWords (prefixCounts x)
attribute [local irreducible] prefixCounts NaturalArray.sumWords
noncomputable def predicate (x : List Bool) : Bool :=
  decide (value (discardPrefix (extractPrefix x))<value (total x))
attribute [local irreducible] total
noncomputable def find (x : List Bool) : List Bool :=
  Find.run predicate (pairBits (x,Indices.run (extractPrefix x)))
noncomputable def searched (x : List Bool) : List Bool := find (pairBits (field 1 x,BinarySeed.normalizeBig (field 2 x)))
attribute [local irreducible] searched
noncomputable def run (x : List Bool) : List Bool := if searched x=[] then field 0 x else (searched x).tail
end MetricKMedianRecovery.BitMachine.BinaryInverseCDF

namespace MetricKMedianRecovery.BitMachine.BinaryDyadic
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
noncomputable def run (x : List Bool) : List Bool := BinaryInverseCDF.run (prepared x)
end MetricKMedianRecovery.BitMachine.BinaryDyadic

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_FinSetDecode
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
variable {n : ℕ}
noncomputable def decode (n : ℕ) (x : List Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i=>BinaryNatSet.contains (pairBits (i.val.bits,x)))
end MetricKMedianRecovery.BitMachine.BinaryFinSet

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
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_CandidateSanitize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
noncomputable def keep (x : List Bool) : Bool :=
  BinaryNatSet.contains (pairBits (discardPrefix x,extractPrefix x))
noncomputable def clip (x : List Bool) : List Bool :=
  filterWith keep (pairBits (field 3 x,field 0 x))
noncomputable def size : List Bool→List Bool := UnaryResources.lengthBits ∘ Count.run ∘ clip
noncomputable def run (x : List Bool) : List Bool :=
  if 0<value (size x) then
    if value (size x)≤value (field 2 x) then clip x else field 1 x
  else field 1 x
variable {n : ℕ}
noncomputable def clipped (F : Finset (Fin n)) (raw : List Bool) : Finset (Fin n) :=
  F.filter (fun i=>BinaryNatSet.contains (pairBits (i.val.bits,raw)))
noncomputable def output (F S : Finset (Fin n)) (k : ℕ) (raw : List Bool) : Finset (Fin n) :=
  if (clipped F raw).Nonempty ∧ (clipped F raw).card≤k then clipped F raw else S
end MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize

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
attribute [local irreducible] advance
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
noncomputable def left (x : List Bool) : List Bool := BinarySeed.nest 4 (pairBits (leftShape x,RawTake.run (pairBits (cut x,discardPrefix x))))
noncomputable def right (x : List Bool) : List Bool := BinarySeed.nest 1 (pairBits (rightShape x,RawDrop.run (pairBits (cut x,discardPrefix x))))
attribute [local irreducible] BinarySeed.nest RawTake.run RawDrop.run cut rightShape tword lword bword
noncomputable def runInput (x : List Bool) : List Bool := encode [field 0 (extractPrefix x),field 1 (extractPrefix x),aword x,tword x,left x]
noncomputable def run (x : List Bool) : List Bool := pairBits (runInput x,right x)
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RationalSurrogate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletion
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
variable {q p r : ℕ}
noncomputable def surrogate (x : List Bool) : List Bool :=
  BinaryRational.encode (BinaryRational.decode (RationalArray.sumWords (clientValues x))+
    BinaryRational.decode (BinaryRationalSort.sumBottom (pairBits (field 0 (extractPrefix x),redValues x))))
noncomputable def saving (x : List Bool) : List Bool :=
  BinaryRational.encode (BinaryRational.decode (surrogate (pairBits (extractPrefix x,[])))-
    BinaryRational.decode (surrogate x))
end MetricKMedianRecovery.BitMachine.BinaryCompletion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionRealize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionRealize
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
variable {n q a p r b : ℕ}
attribute [local irreducible] fillInput BinaryCompletionFill.run BinaryFinSet.image
noncomputable def redIndices (x : List Bool) : List Bool := BinaryNatSet.sort
  (BinaryRationalSort.rawIndices (pairBits (field 0 (field 10 x),redValues x)))
attribute [local irreducible] redValues BinaryNatSet.sort BinaryRationalSort.rawIndices
noncomputable def red (x : List Bool) : List Bool := BinaryFinSet.image (pairBits (field 6 x,redIndices x))
attribute [local irreducible] redIndices
noncomputable def removed (x : List Bool) : List Bool := BinaryNatSet.union
  (pairBits (BinaryNatSet.union (pairBits (field 2 x,red x)),blue x))
attribute [local irreducible] red blue dest BinaryNatSet.union
noncomputable def remain (x : List Bool) : List Bool := BinaryNatSet.diff (pairBits (field 1 x,removed x))
attribute [local irreducible] removed BinaryNatSet.diff
attribute [local irreducible] filled
noncomputable def core (x : List Bool) : List Bool := BinaryNatSet.union (pairBits (remain x,added x))
attribute [local irreducible] remain added
noncomputable def runInput (x : List Bool) : List Bool := encode [field 0 x,core x,lengthBits (field 1 x)]
attribute [local irreducible] core
noncomputable def run (x : List Bool) : List Bool := BinaryCompletionPad.run (runInput x)
end MetricKMedianRecovery.BitMachine.BinaryCompletionRealize

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
open BinaryOpeningPayment (field field_computes )
open Categorical.Explicit
variable {n q a p r c : ℕ}
noncomputable def prepared (x : List Bool) : List Bool := BinaryCategorical.Prepare.run (pairBits (context x,discardPrefix x))
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
open BinaryOpeningPayment (field field_computes )
attribute [local irreducible] Count.run BinaryBisection.logWord RawTake.run RawDrop.run BinaryColorLabel.colors BinaryColorLabel.labels
noncomputable def blog (x : List Bool) : List Bool := BinaryBisection.logWord (lengthBits (field 8 x))
noncomputable def lshape (x : List Bool) : List Bool := encode [nword x,blog x]
noncomputable def lsize (x : List Bool) : List Bool :=
  (value (UnaryResources.lengthBits (nword x))*value (UnaryResources.lengthBits (blog x))).bits
noncomputable def craw (x : List Bool) : List Bool := RawTake.run (pairBits (csize (extractPrefix x),discardPrefix x))
noncomputable def lraw (x : List Bool) : List Bool := RawTake.run (pairBits (lsize (extractPrefix x),rest x))
noncomputable def tailBits (x : List Bool) : List Bool := RawDrop.run (pairBits (lsize (extractPrefix x),rest x))
noncomputable def colors (x : List Bool) : List Bool := BinaryColorLabel.colors (pairBits (cshape (extractPrefix x),craw x))
noncomputable def labels (x : List Bool) : List Bool := BinaryColorLabel.labels
  (pairBits (lengthBits (field 8 (extractPrefix x)),pairBits (lshape (extractPrefix x),lraw x)))
noncomputable def context (x : List Bool) : List Bool :=
  encode [field 0 (extractPrefix x),field 1 (extractPrefix x),field 2 (extractPrefix x),field 3 (extractPrefix x),
    field 4 (extractPrefix x),field 5 (extractPrefix x),colors x,labels x,field 8 (extractPrefix x),
    field 9 (extractPrefix x),field 10 (extractPrefix x),field 11 (extractPrefix x)]
end MetricKMedianRecovery.BitMachine.BinaryBranchRandomize

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
attribute [local irreducible] finalCount

noncomputable def leftLength : List Bool → List Bool := lengthBits ∘ extractPrefix ∘ leftNode
noncomputable def rightLength : List Bool → List Bool := lengthBits ∘ extractPrefix ∘ rightNode
noncomputable def mixedCount (x : List Bool) : List Bool := finalCount (pairBits (extractPrefix x,mixed x))
noncomputable def directed (x : List Bool) : List Bool :=
  if decide (value (leftLength x)=value (rightLength x)) then
    if decide (value (mixedCount x)=value (cf 2 x)) then successNode (mixed x) else mixedCommon x
  else taggedPair 2 (discardPrefix x)
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
attribute [local irreducible] finalCount 
noncomputable def leftCount : List Bool → List Bool := finalCount ∘ leftData
noncomputable def rightCount : List Bool → List Bool := finalCount ∘ rightData
noncomputable def sandwiched (x : List Bool) : Bool :=
  (decide (value (leftCount x)<value (cf 2 x)) && decide (value (cf 2 x)<value (rightCount x))) ||
  (decide (value (rightCount x)<value (cf 2 x)) && decide (value (cf 2 x)<value (leftCount x)))
end MetricKMedianRecovery.BitMachine.BinaryCross

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
noncomputable def padded (x : List Bool) : List Bool :=
  BinaryCompletionPad.run (encode [field 2 x,field 3 x,target x])
noncomputable def localInput (x : List Bool) : List Bool :=
  encode [field 0 x,field 1 x,map BinaryProjection.originalWord (field 2 x),BinaryProjection.lift (padded x)]
noncomputable def run : List Bool→List Bool := BinaryProjection.run ∘ BinaryLocalRefine.run ∘ localInput
end MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess

end OAI
end


