-- Prove2me | Definitions.Def_Q238L025
-- name    : Q238L025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:25:57.960027+00:00
-- url     : https://prove2.me/theorems/60457695-9cce-43f3-a107-ad6202d9517b
-- title:
--   Definitions bundle Q238L025 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 119 declarations of OpenAI's Lean: 114 definitions, 1 inductive type or structure and 4 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryClassFilter.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionPad.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCorrection.applyWord`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCorrection.encode`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCorrection.mapHistory`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCorrection.mapRow`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.endLeaf`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.leafPack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.leafPrefix`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.mapPrefix`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.outcomeBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.outputBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.stateBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledState.encode`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.fallbackInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.mappedPrefix`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.nonempty`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.prefixG`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.ctxBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.nodeBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.resultBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.accBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix.twice_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.counts`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.prepared`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.setBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.historyBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.P.budget`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.bracketInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.far`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.high` and 75 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_GlobalOuter`, `KMedianRecovery_Algorithms_IntegralRecoveryGuesses`, `KMedianRecovery_Algorithms_IntegralRecoveryMachine`, `KMedianRecovery_Algorithms_IntegralRecoveryRepeat`, `KMedianRecovery_Branching_BranchTapeBound`, `KMedianRecovery_Branching_CompletionFillMath`, `KMedianRecovery_Branching_CompletionRealize`, `KMedianRecovery_Branching_CopyGround`, `KMedianRecovery_Encoding_ColorLabelMachine`, `KMedianRecovery_Encoding_CoupledEncode`, `KMedianRecovery_Encoding_DuplicateMatrix`, `KMedianRecovery_Encoding_FinSets`, `KMedianRecovery_Encoding_LabelLookup`, `KMedianRecovery_Encoding_RationalStream`, `KMedianRecovery_Encoding_StateBits2`, `KMedianRecovery_Encoding_UnaryParser`, `KMedianRecovery_Encoding_WordExtras`, `KMedianRecovery_Geometry_LocalBest`, `KMedianRecovery_Geometry_MetricAnchor`, `KMedianRecovery_Geometry_MetricArrays`, `KMedianRecovery_Geometry_MetricCost2`, `KMedianRecovery_Geometry_MetricParser`, `KMedianRecovery_Geometry_NearestLeafMachine`, `KMedianRecovery_Geometry_RoundingMatrix`, `KMedianRecovery_Machines_CoupledPrimitives`, `KMedianRecovery_Machines_DeleteFold`, `KMedianRecovery_Machines_DeleteSize`, `KMedianRecovery_Machines_FiniteMachine`, `KMedianRecovery_Machines_InitialLoop`, `KMedianRecovery_Machines_LengthQuery`, `KMedianRecovery_Machines_LoopInvariant`, `KMedianRecovery_Machines_LoopMachine`, `KMedianRecovery_Machines_MatchFold`, `KMedianRecovery_Machines_MatchSize`, `KMedianRecovery_Machines_MenuMachine`, `KMedianRecovery_Machines_ProjectionMachine`, `KMedianRecovery_Machines_RefineMachine`, `KMedianRecovery_Machines_ScanMachine`, `KMedianRecovery_Machines_SensitiveMachine`, `KMedianRecovery_Machines_StepMachine`, `KMedianRecovery_Recovery_ClassFilter`, `KMedianRecovery_Recovery_CrossCount`, `KMedianRecovery_Recovery_CrossEdge`, `KMedianRecovery_Recovery_FiniteContext`, `KMedianRecovery_Recovery_FirstPresent`, `KMedianRecovery_Recovery_InitialAuto`, `KMedianRecovery_Recovery_InitialCorrect`, `KMedianRecovery_Recovery_LengthCandidates`, `KMedianRecovery_Recovery_NormalizeInput`, `KMedianRecovery_Recovery_RecoveryEnumeration`, `KMedianRecovery_Recovery_RefineMath`, `KMedianRecovery_Sampling_InverseCDF`, `KMedianRecovery_Sampling_SamplerParameters`, `KMedianRecovery_Sampling_SamplerUpdateParts`, `KMedianRecovery_Sampling_SamplerWeights`, `KMedianRecovery_Strictness_MetricSurplus`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L013`, `Q238L014`, `Q238L015`, `Q238L016`, `Q238L017`, `Q238L018`, `Q238L019` and `Q238L020` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L029`, `Q238L030` and `Q238L031`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.copyData_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.added_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.locations_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.countInter_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.union_list_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.run_code_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.badBalls_nil_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.copyData_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.locations_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.origins_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.parts_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.added_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.locations_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.countInter_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.union_list_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.run_code_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L013
import Definitions.Def_Q238L014
import Definitions.Def_Q238L015
import Definitions.Def_Q238L016
import Definitions.Def_Q238L017
import Definitions.Def_Q238L018
import Definitions.Def_Q238L019
import Definitions.Def_Q238L020

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabelLookup
open WordOperations WordList RationalLeaves

noncomputable def history : List Bool → List Bool := mapWith run
end MetricKMedianRecovery.BitMachine.BinaryLabelLookup

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

def setBits {m : ℕ} (S : Finset (Label (Fin m))) : List Bool := labels (orderedSort S)
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

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
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels)

def historyBits {m : ℕ} (hs : List (List (Label (Fin m)))) : List Bool := encode (hs.map labels)
end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations BinaryArithmetic RationalLeaves
noncomputable def copied (x : List Bool) : List Bool :=
  if value (levelWords (discardPrefix x))=0 then
    pairBits ((value (extractPrefix x)+1).bits,pairBits (parentWords (discardPrefix x),BinaryRational.encode 0))
  else discardPrefix x

noncomputable def swapped (x : List Bool) : List Bool :=
  if eq (pairBits (discardPrefix x,extractPrefix (extractPrefix x))) then discardPrefix (extractPrefix x)
  else if eq (pairBits (discardPrefix x,discardPrefix (extractPrefix x))) then extractPrefix (extractPrefix x)
  else discardPrefix x
end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field )
lemma labels_append {m : ℕ} (xs ys : List (Label (Fin m))) : labels (xs++ys)=labels xs++labels ys := by
  simp only [labels,List.map_append,encode_append]
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

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
noncomputable def copied (x : List Bool) : List Bool := BinaryLabel.copied (pairBits (cf 2 x,jf 4 x))
noncomputable def source (x : List Bool) : List Bool :=
  if tagIs 0 x then cf 3 x else jf 1 x++cons (if tagIs 1 x then jf 4 x else copied x) (jf 2 x)
noncomputable def target (x : List Bool) : List Bool :=
  if tagIs 0 x then cf 3 x++cons (copied x) [] else
    if tagIs 1 x then (jf 1 x++jf 2 x)++jf 3 x else jf 1 x++cons (jf 4 x) (jf 2 x)

end MetricKMedianRecovery.BitMachine.BinaryJump

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
open BinaryOpeningPayment (field )
def pack (F U : Finset ℕ) (n : ℕ) : List Bool :=
  encode [BinaryNatSet.encode F,BinaryNatSet.encode U,n.bits]
end MetricKMedianRecovery.BitMachine.BinaryCompletionPad

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

lemma mass_next (x : List Bool) : mass (next x) ≤ mass x := by
  unfold next While.next
  split_ifs
  · unfold step
    cases hd : data x with
    | nil=>simp only [List.head?_nil,Option.getD_none,Bool.false_eq_true,ite_false, if_false,mass,counter_pack,
        data_pack,output_pack,List.tail_nil,List.length_nil,hd]; omega
    | cons b d=>cases b <;>
      simp only [List.head?_cons,Option.getD_some,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,mass,
        counter_pack,data_pack,output_pack,List.tail_cons,List.length_nil,List.length_cons,hd] <;> omega
  · exact le_rfl
lemma length_next (x : List Bool) : (next x).length ≤ max x.length (2*mass (next x)+3) := by
  unfold next While.next
  split_ifs
  · unfold step
    split_ifs <;> simp only [length_pack,mass,counter_pack,data_pack,output_pack,List.length_nil] <;> omega
  · exact Nat.le_max_left _ _
end MetricKMedianRecovery.BitMachine.UnaryParser

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser
open WordOperations
attribute [local irreducible] UnaryParser.run UnaryTake.takeWords UnaryTake.dropWords
noncomputable def nat (x : List Bool) : List Bool :=
  pairBits (UnaryTake.takeWords (UnaryParser.run x),UnaryTake.dropWords (UnaryParser.run x))
attribute [local irreducible] nat
noncomputable def numerator (x : List Bool) : List Bool :=
  x.head?.getD false::extractPrefix (nat x.tail)
noncomputable def denominator (x : List Bool) : List Bool := nat (discardPrefix (nat x.tail))
attribute [local irreducible] numerator denominator
noncomputable def rational (x : List Bool) : List Bool :=
  pairBits (pairBits (numerator x,extractPrefix (denominator x)),discardPrefix (denominator x))
end MetricKMedianRecovery.BitMachine.BinaryInputParser

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream
open WordOperations
noncomputable def step (x : List Bool) : List Bool :=
  if extractPrefix x=[] then x else
    pairBits (discardPrefix (rational (extractPrefix x)),
      WordList.cons (extractPrefix (rational (extractPrefix x))) (discardPrefix x))
attribute [local irreducible] rational
noncomputable def run (x : List Bool) : List Bool :=
  WordList.reverse (discardPrefix (BoundedIteration.polynomialRun step Polynomial.X (3*Polynomial.X+1) (pairBits (x,[]))))
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream

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
attribute [local irreducible] nat RawDrop.run Stream.run RawUnary.run
noncomputable def header (x : List Bool) : List Bool := nat x
noncomputable def count (x : List Bool) : List Bool := extractPrefix (header x)
noncomputable def tailHeader (x : List Bool) : List Bool := nat (discardPrefix (header x))
noncomputable def budget (x : List Bool) : List Bool := extractPrefix (tailHeader x)
noncomputable def masks (x : List Bool) : List Bool := discardPrefix (tailHeader x)
noncomputable def afterClients (x : List Bool) : List Bool := RawDrop.run (pairBits (count x,masks x))
noncomputable def rawMatrix (x : List Bool) : List Bool := RawDrop.run (pairBits (count x,afterClients x))
attribute [local irreducible] header count tailHeader budget masks afterClients rawMatrix
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric

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
noncomputable def member (x : List Bool) : Bool :=
  (RawDrop.run (pairBits (discardPrefix x,extractPrefix x))).head?.getD false
end MetricKMedianRecovery.BitMachine.BinaryMaskParser

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyGround
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCopyTables
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n a : ℕ}
def pack (H : Fin a→Finset (Fin n)) : List Bool :=
  encode [List.replicate n true,encode (List.ofFn (fun i=>BinaryFinSet.encode (H i)))]
attribute [local irreducible] mapWith flatMapWith
end MetricKMedianRecovery.BitMachine.BinaryCopyTables

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_ColorLabelMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalPower
open WordOperations WordList RationalHeight
noncomputable def op (x : List Bool) : List Bool := BinaryRational.encode
  (BinaryRational.decode (extractPrefix x)*BinaryRational.decode (discardPrefix (discardPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryRationalPower

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
open BinaryOpeningPayment (field )
noncomputable def divide (x : List Bool) : List Bool := BinaryRational.encode
  (BinaryRational.decode (discardPrefix x)/BinaryRational.decode (extractPrefix x))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryMenu

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_NearestLeafMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNearestLeaf
open WordOperations WordList BinaryArithmetic
variable {n : ℕ}
noncomputable def distances (x : List Bool) : List Bool := mapWith (fun z=>BinaryRational.encode (distance z)) x
noncomputable def run (x : List Bool) : List Bool :=
  if empty x then [] else encode [RationalMin.run (distances x)]
end MetricKMedianRecovery.BitMachine.BinaryNearestLeaf

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_InverseCDF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDyadic
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )

def pack (b d : ℕ) (ps : List ℚ) (raw : List Bool) : List Bool :=
  encode [List.replicate b true,RationalArray.encode ps,d.bits,raw]
noncomputable def counts (x : List Bool) : List Bool :=
  mapWith count (pairBits (BinaryRational.encode (scale (field 0 x)),field 1 x))
noncomputable def prepared (x : List Bool) : List Bool := encode [field 2 x,counts x,field 3 x]
end MetricKMedianRecovery.BitMachine.BinaryDyadic

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Weights
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def active (x : List Bool) : Bool :=
  !(decide (c 3 x=[])) && decide (0<BinaryRational.decode (c 1 x))
end MetricKMedianRecovery.BitMachine.BinarySampler.Weights

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerUpdateParts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Update
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
open Weights (actionField )
variable {n : ℕ}
noncomputable def input (x : List Bool) : List Bool := Weights.stateInput (extractPrefix x)
noncomputable def clientInput (x : List Bool) : List Bool := pairBits (input x,actionField 1 x)
end MetricKMedianRecovery.BitMachine.BinarySampler.Update

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
open BinaryOpeningPayment (field )
variable {n p q : ℕ}
noncomputable def column (x : List Bool) : List Bool := BinaryIndexMap.run
  (pairBits (row x,field 2 (extractPrefix x)))
attribute [local irreducible] BinaryIndexMap.run
noncomputable def run (x : List Bool) : List Bool := mapWith column (pairBits (x,field 1 x))
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
noncomputable def near (x : List Bool) : List Bool := RationalMin.run (discardPrefix x)
noncomputable def run (x : List Bool) : List Bool := RationalArray.sumWords
  (mapWith near (pairBits ([],BinaryMetricArrays.run x)))
end MetricKMedianRecovery.BitMachine.BinaryMetricCost

namespace MetricKMedianRecovery.BitMachine.BinaryMetricBest
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def score (x : List Bool) : List Bool := BinaryRational.negWords (BinaryMetricCost.run
  (encode [field 0 (extractPrefix x),field 1 (extractPrefix x),discardPrefix x]))
end MetricKMedianRecovery.BitMachine.BinaryMetricBest

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
open BinaryOpeningPayment (field )
variable {n q a p r b : ℕ}
def pack (F S Q : Finset (Fin n)) (part : Fin q→Fin a) (o : Fin a→Fin q) (loc : Fin q→Fin n)
    (redLoc : Fin r→Fin n) (blueLoc blueDest : Fin b→Fin n) (k : ℕ)
    (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ) (weight redBase : Fin r→ℚ)
    (redDistance : Fin r→Fin q→ℚ) (xs : List (Fin q)) : List Bool :=
  encode [BinaryFinSet.encode F,BinaryFinSet.encode S,BinaryFinSet.encode Q,
    BinaryFinSet.table part,BinaryFinSet.table o,BinaryFinSet.table loc,
    BinaryFinSet.table redLoc,BinaryFinSet.table blueLoc,BinaryFinSet.table blueDest,
    encode (xs.map BinaryCategorical.elemBits),BinaryCompletion.contextBits k base distance weight redBase redDistance]
attribute [local irreducible] fillInput
end MetricKMedianRecovery.BitMachine.BinaryCompletionRealize

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ClassFilter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryClassFilter
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ}
def pack (S : Finset (Fin n)) (label : Fin n→Fin m) (c : Fin m) : List Bool :=
  pairBits (pairBits (BinaryFinSet.table label,c.val.bits),BinaryFinSet.encode S)
end MetricKMedianRecovery.BitMachine.BinaryClassFilter

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
open BinaryOpeningPayment (field )
attribute [local irreducible] zeroContext
noncomputable def choices (x : List Bool) : List Bool := cross (pairBits (range x,cross (pairBits (range x,blueRange x))))
attribute [local irreducible] mapWith
attribute [local irreducible] metricContext
end MetricKMedianRecovery.BitMachine.BinaryRecovery

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
open BinaryOpeningPayment (field )
attribute [local irreducible] bound
noncomputable def diameter (x : List Bool) : List Bool := BinaryRational.natWords (field 5 x)
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
open BinaryOpeningPayment (field )
attribute [local irreducible] src extra completeRaw BinaryRational.natWords
attribute [local irreducible] mapWith
noncomputable def metricContext (x : List Bool) : List Bool := encode [src 0 x,src 2 x]
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

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
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryRepeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat
open WordOperations WordList Sampling.Comparison
attribute [local irreducible] extra Fair.raw RawUnary.run BinaryFinSet.encode BinaryMetricBest.best List.ofFn BinarySeed.raw
noncomputable def context (x : List Bool) : List Bool := pairBits (extractPrefix x,extra x)
attribute [local irreducible] mapWith
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
open BinaryOpeningPayment (field )
attribute [local irreducible] BinaryFinSet.encode Count.run src
noncomputable def price (x : List Bool) : List Bool := BinaryRational.natWords (extractPrefix (discardPrefix x))
noncomputable def atParams (x : List Bool) : List Bool := encode
  [source 0 x,source 1 x,source 2 x,source 3 x,source 4 x,source 5 x,price x,count x]
noncomputable def atInput (x : List Bool) : List Bool := pairBits (atParams x,pairBits
  (extra (extractPrefix x),Fair.raw (extractPrefix x)))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

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
open BinaryOpeningPayment (field )

def ctxBits {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ) : List Bool := encode [setBits F,setBits Q,k.bits]
def nodeBits {m : ℕ} (P : List (Label (Fin m)) × List (List (Label (Fin m)))) : List Bool :=
  pairBits (labels P.1,historyBits P.2)
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
noncomputable def newLeaf (x : List Bool) : List Bool :=
  pairBits ((value (cf 3 x)+1).bits,pairBits (BinaryLabel.parentWords (cf 4 x),discardPrefix x))
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
noncomputable def early (x : List Bool) : List Bool := encode [(0:ℕ).bits,BinaryRational.encode 0,[],small x,[]]
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
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalBest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalBest
open WordOperations WordList BinaryArithmetic
noncomputable def run (rank : List Bool→List Bool) (x : List Bool) : List Bool :=
  CappedFold.run (choose rank) (pairBits (x,Fold.pack (discardPrefix (discardPrefix x)) (extractPrefix x)
    (extractPrefix (discardPrefix x))))
end MetricKMedianRecovery.BitMachine.BinaryLocalBest

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
noncomputable def originalWord (x : List Bool) : List Bool :=
  pairBits ((0:ℕ).bits,pairBits (x,BinaryRational.encode 0))
end MetricKMedianRecovery.BitMachine.BinaryProjection

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
open BinaryOpeningPayment (field )
attribute [local irreducible] BinaryMetricArrays.run
variable {n : ℕ}
noncomputable def rectangle : List Bool→List Bool := BinaryMetricArrays.run ∘ rectInput
noncomputable def anchorInput (x : List Bool) : List Bool := encode [rectangle x,Count.run (field 2 x),
  map BinaryProjection.originalWord (field 3 x),field 4 x]
attribute [local irreducible] WordList.map
attribute [local semireducible] WordList.map
end MetricKMedianRecovery.BitMachine.BinaryMetricAnchor

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
noncomputable def applyWord (x : List Bool) : List Bool :=
  if extractPrefix x=[] then discardPrefix x else BinaryLabel.swapped x
noncomputable def mapRow : List Bool→List Bool := mapWith applyWord
noncomputable def mapHistory : List Bool→List Bool := mapWith mapRow
end MetricKMedianRecovery.BitMachine.BinaryCorrection

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
def stateBits {m : ℕ} (s : State (Fin m)) : List Bool :=
  encode [setBits s.B,historyBits s.P,BinaryCorrection.encode s.correction,
    BinaryRational.encode s.lam,BinaryRational.encode s.lam',historyBits s.T,historyBits s.U]
def outputBits {m : ℕ} (o : Output (Fin m)) : List Bool := encode [setBits o.B,BinaryRational.encode o.lam,historyBits o.P]
def outcomeBits {m : ℕ} : Outcome (Fin m)→List Bool
 | .inl o=>pairBits ([],outputBits o)
 | .inr s=>pairBits ([true],stateBits s)
noncomputable def mapPrefix (x : List Bool) : List Bool := BinaryCorrection.mapHistory (pairBits (field 2 x,field 1 x))
attribute [local irreducible] BinaryCorrection.mapHistory
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves RationalHeight
variable {V : Type*} [LinearOrder V] {d : ℕ}
structure Frame (V : Type*) where
  q : ℕ
  n : ℕ
  out : Outcome V

attribute [local instance] RationalLeaves.metric

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CrossEdge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCross
open WordOperations WordList RationalLeaves BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field )

def resultBits {m : ℕ} : CanonicalMergeCrossing.Result (Label (Fin m)) → List Bool
  | .success H T=>encode [(0:ℕ).bits,nodeBits (H,T),[]]
  | .common H T U=>encode [(1:ℕ).bits,nodeBits (H,T),historyBits U]
  | .sensitive H G T U=>encode [(2:ℕ).bits,nodeBits (H,T),nodeBits (G,U)]
def pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (P R : List (Label (Fin m)) × List (List (Label (Fin m)))) : List Bool :=
  pairBits (ctxBits F Q k,pairBits (nodeBits P,nodeBits R))
end MetricKMedianRecovery.BitMachine.BinaryCross

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
open BinaryOpeningPayment (field )
attribute [local irreducible] WordList.mapWith
noncomputable def frees (x : List Bool) : List Bool := crossWith freeOp (pairBits (field 1 x,field 3 x))
end MetricKMedianRecovery.BitMachine.BinaryLength

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CoupledPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field )
noncomputable def makeLeaf (x : List Bool) : List Bool :=
  pairBits ((value (field 0 x)+1).bits,pairBits (parentWords (field 1 x),field 2 x))
end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

def leafPack {m : ℕ} (B : Finset (Label (Fin m))) (P : List (List (Label (Fin m)))) (lam : ℚ)
    (key : ℕ) (i : Label (Fin m)) (C : List (Label (Fin m))) (l u : ℚ) (T U : List (List (Label (Fin m)))) : List Bool :=
  encode [setBits B,historyBits P,BinaryRational.encode lam,key.bits,BinaryLabel.encode i,labels C,
    BinaryRational.encode l,BinaryRational.encode u,historyBits T,historyBits U]
noncomputable def endLeaf (j : ℕ) (x : List Bool) : List Bool := BinaryLabel.makeLeaf (encode [field 3 x,field 4 x,field j x])
noncomputable def leafPrefix (x : List Bool) : List Bool := field 1 x++cons (field 5 x++cons (endLeaf 7 x) []) []
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_DeleteFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDelete
open WordOperations WordList RationalLeaves CanonicalDelete
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field )

def accBits {m : ℕ} (s : Acc (Label (Fin m))) : List Bool :=
  encode [labels s.remaining,labels s.extras,historyBits s.vertices]
end MetricKMedianRecovery.BitMachine.BinaryDelete

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_DeleteSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDelete
open WordOperations WordList RationalLeaves CanonicalDelete
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

def pack {m : ℕ} (base : List Bool) (C : List (Label (Fin m))) (ci : Label (Fin m))
    (U E : List (Label (Fin m))) : List Bool :=
  Fold.pack (labels U) (contextBits base (labels C) (BinaryLabel.encode ci)) (accBits ⟨U,E,[]⟩)

end MetricKMedianRecovery.BitMachine.BinaryDelete

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
noncomputable def spareWord (x : List Bool) : List Bool := BinaryLabel.copied (pairBits (cf 0 x,jf 4 x))
noncomputable def ctSpare (x : List Bool) : List Bool := ct x++cons (spareWord x) []
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
open BinaryOpeningPayment (field )
noncomputable def target : List Bool → List Bool := head ∘ cutTail
noncomputable def jumpContext (x : List Bool) : List Bool := encode [cf 0 x,cf 1 x,cf 2 x,source x,target x]
noncomputable def edgeInput (x : List Bool) : List Bool := encode [jumpContext x,cf 3 x]
end MetricKMedianRecovery.BitMachine.BinaryRefine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FirstPresent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.FirstPresent
open WordOperations
open CanonicalMergeCrossing
noncomputable def found (x : List Bool) : List Bool := Find.run present (pairBits ([],discardPrefix x))
noncomputable def run (x : List Bool) : List Bool := if found x=[] then extractPrefix x else (found x).tail.tail
end MetricKMedianRecovery.BitMachine.WordList.FirstPresent

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ScanMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteCross
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field )
def pack {m : ℕ} (base : List Bool) (key spare k n q : ℕ) (H G : List (Label (Fin m)))
    (T U : List (List (Label (Fin m)))) : List Bool :=
  encode [base,key.bits,spare.bits,k.bits,List.replicate n true,List.replicate q true,labels H,labels G,historyBits T,historyBits U]
end MetricKMedianRecovery.BitMachine.BinaryFiniteCross

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
noncomputable def mappedPrefix (x : List Bool) : List Bool := BinaryCoupled.mapPrefix (field 6 x)
noncomputable def prefixG (x : List Bool) : List Bool := mappedPrefix x++cons (G x) []
noncomputable def fallbackInput (x : List Bool) : List Bool := encode [sf 0 x,sf 3 x,sf 1 x,(fun _=>[]) x]
noncomputable def nonempty (x : List Bool) : Bool := (!(decide (sf 5 x=[]))) && (!(decide (sf 6 x=[])))
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
noncomputable def high (x : List Bool) : List Bool := BinaryRational.encode
  (8*((field 1 (field 0 x)).length:ℚ)*BinaryRational.decode (field 6 x))
noncomputable def far (x : List Bool) : List Bool := BinaryRational.encode
  (20*((field 1 x).length:ℚ)*BinaryRational.decode (field 6 x))

noncomputable def bracketInput (x : List Bool) : List Bool := encode [(field 2) x,(ctx) x,(field 4) x,(field 5) x,(high) x]

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

def step (K : ℚ) (x : List Bool) : List Bool :=
  if threshold x ≤ power x then x else
    pairBits (extractPrefix x,pairBits (BinaryRational.encode (K*power x),true::count x))

def coefficient (K : ℚ) (C : ℕ) : ℕ := 6*C*(BinaryRational.encode K).length+C+16

def initial (x : List Bool) : List Bool := pairBits (x,pairBits (BinaryRational.encode 1,[]))

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
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
noncomputable def low (x : List Bool) : List Bool := BinaryRational.encode (2/((size x).length:ℚ)^2)
noncomputable def threshold (x : List Bool) : List Bool := BinaryRational.encode
  (BinaryRational.decode (field 4 x)+8*((field 1 x).length:ℚ)*BinaryRational.decode (field 4 x))
end MetricKMedianRecovery.BitMachine.BinaryInitialAuto

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
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def rectangle : List Bool→List Bool := BinaryMetricAnchor.rectangle ∘ anchorInput
noncomputable def initial (x : List Bool) : List Bool := encode [rectangle x,Count.run (field 2 x),field 3 x,field 2 x,
  BinaryRational.natWords (field 4 x),field 5 x]
noncomputable def runInput (x : List Bool) : List Bool := pairBits (initial x,total x)
end MetricKMedianRecovery.BitMachine.BinaryMetricSurplus

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
noncomputable def run : List Bool→List Bool := twice ∘ map twice

end MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_RoundingMatrix
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def distance (x : List Bool) : List Bool :=
  MetricTable.get (pairBits (pairBits (field 0 (ctx x),rowIndex x),colIndex x))
noncomputable def entryInput (x : List Bool) : List Bool := encode [distance x,field 2 (ctx x),field 3 (ctx x)]
noncomputable def entry (x : List Bool) : List Bool :=
  if value (rowIndex x)=value (colIndex x) then BinaryRational.encode 0 else BinaryRound.rational (entryInput x)
noncomputable def row (x : List Bool) : List Bool :=
  mapWith entry (pairBits (x,BinaryEllipsoidInitial.indices (field 1 (extractPrefix x))))
noncomputable def run (x : List Bool) : List Bool :=
  mapWith row (pairBits (x,BinaryEllipsoidInitial.indices (field 1 x)))
end MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix

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
open BinaryOpeningPayment (field )
attribute [local irreducible] BinaryInputParser.Metric.count BinaryInputParser.Metric.budget

noncomputable def count (x : List Bool) : List Bool := BinaryInputParser.Metric.count (raw x)
noncomputable def budget (x : List Bool) : List Bool := BinaryInputParser.Metric.budget (raw x)
end MetricKMedianRecovery.BitMachine.BinaryNormalizeInput

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
open BinaryOpeningPayment (field )
namespace P
noncomputable abbrev budget := BinaryInputParser.Metric.budget
end P
attribute [local irreducible] BinaryInputParser.Metric.budget
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end


