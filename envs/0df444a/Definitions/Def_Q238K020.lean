-- Prove2me | Definitions.Def_Q238K020
-- name    : Q238K020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:16:00.407519+00:00
-- url     : https://prove2.me/theorems/10a1bee0-4837-417a-8c85-9549b96b494a
-- title:
--   Definitions bundle Q238K020 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 85 declarations of OpenAI's Lean: 61 definitions and 24 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.atCall`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.atCenter`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.block`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.bad`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.contents`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.result`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCollect.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLookup.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Seed`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.completionCount`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.count`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.layout`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.raw`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.advance`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.advanceItem`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.drawItems`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.marginal`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.marginalDraw`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.marginalValues`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.cap`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.clientValues`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.redValues`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.weightedCap`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.redValues`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.parts`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCorrection.applyWord`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCorrection.mapHistory`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCorrection.mapRow`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.mapPrefix`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.mappedPrefix`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.prefixG`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.containsItem`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.loInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.pack` and 21 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_CandidateSanitize`, `KMedianRecovery_Branching_BlueBlocksMachine`, `KMedianRecovery_Branching_BlueChoice`, `KMedianRecovery_Branching_BlueDPValue`, `KMedianRecovery_Branching_BlueLookup`, `KMedianRecovery_Branching_BlueMerge`, `KMedianRecovery_Branching_BlueNextTable`, `KMedianRecovery_Branching_BluePlan`, `KMedianRecovery_Branching_BranchContext`, `KMedianRecovery_Branching_BranchObjective`, `KMedianRecovery_Branching_BranchSeedLayout`, `KMedianRecovery_Branching_CategoricalScore`, `KMedianRecovery_Branching_CategoricalTable`, `KMedianRecovery_Branching_CompletionRealize`, `KMedianRecovery_Branching_CopyGround`, `KMedianRecovery_Branching_FavorableReady`, `KMedianRecovery_Branching_RationalSurrogate`, `KMedianRecovery_Encoding_CoupledEncode`, `KMedianRecovery_Encoding_LabelLookup`, `KMedianRecovery_Encoding_LabelMember`, `KMedianRecovery_Encoding_RationalBest`, `KMedianRecovery_Encoding_RationalCap`, `KMedianRecovery_Encoding_RationalSort`, `KMedianRecovery_Encoding_WordExtras`, `KMedianRecovery_Machines_FiniteMachine`, `KMedianRecovery_Machines_InitialLoop`, `KMedianRecovery_Machines_StepMachine`, `KMedianRecovery_Recovery_CrossCount`, `KMedianRecovery_Recovery_InitialAuto`, `KMedianRecovery_Recovery_Min`, `KMedianRecovery_Recovery_Rectangular`, `KMedianRecovery_Recovery_RefineMath`, `KMedianRecovery_Recovery_Step`, `KMedianRecovery_Sampling_SamplingReference`, `KMedianRecovery_Strictness_SurplusPostprocess`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K007`, `Q238K008`, `Q238K010`, `Q238K011` and `Q238K012` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K025`, `Q238K026` and `Q238K027`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.at_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.marginal_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.transposed_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.ranked_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingReference.entries_pack_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinaryZeroBranch_successful_probability_s238`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.at_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueSize.tableRun_best_bound_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueSize.table_length_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.marginal_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.gram_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.rhs_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.transposed_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Fair_output_exponential_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.ranked_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingReference.entries_pack_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinaryZeroBranch_successful_probability_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K007
import Definitions.Def_Q238K008
import Definitions.Def_Q238K010
import Definitions.Def_Q238K011
import Definitions.Def_Q238K012

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open UnaryTake
namespace BoundedIteration

lemma run_eq (f : List Bool → List Bool) (c d s : List Bool)
    (h : ∀ j, j ≤ c.length → (f^[j] s).length ≤ d.length) :
    run f (pairBits (c,pairBits (d,s)))=f^[c.length] s := by
  rw [run_pair]; exact clamp_iterate_eq f d.length c.length s h

end BoundedIteration
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Rectangular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open BinaryArithmetic Matrix
namespace Rectangular
open WordList RationalMatrix

def encode {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : List Bool :=
  WordList.encode (List.ofFn (fun i=>rowEncode (A i)))
end Rectangular
end

open BinaryArithmetic RationalLinearFeasibility Ellipsoid Matrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Min
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic WordList
namespace BinaryPhaseAdvance
open EffectiveOpenability RationalPhase BinaryOpeningPayment

noncomputable def nearest (x : List Bool) : ℚ :=
  BinaryRational.decode (BinaryOpeningNearest.run (BinaryOpeningPayment.activityInput (query x)))
noncomputable def clippedItem (x : List Bool) : ℚ :=
  if sf 1 (extractPrefix x)=[] then phase (extractPrefix x)
  else min (phase (extractPrefix x)) ((1-3*paramV (extractPrefix x))*nearest x)
end BinaryPhaseAdvance
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelMember
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open BinaryArithmetic WordList RationalLeaves

noncomputable def contains (x : List Bool) : Bool := decide (Find.run eq x≠[])

end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryLabelSelect
open Classical
open BinaryArithmetic WordList RationalLeaves EffectiveOpenability

noncomputable def test (x : List Bool) : Bool :=
  BinaryLabel.contains (pairBits (Lookup.run (pairBits (index x,alphabet x)),target x))
end MetricKMedianRecovery.BitMachine.BinaryLabelSelect

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
open WordList RationalLeaves

noncomputable def history : List Bool → List Bool := mapWith run
end MetricKMedianRecovery.BitMachine.BinaryLabelLookup

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_FiniteMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open BinaryArithmetic RationalLeaves
noncomputable def copied (x : List Bool) : List Bool :=
  if value (levelWords (discardPrefix x))=0 then
    pairBits ((value (extractPrefix x)+1).bits,pairBits (parentWords (discardPrefix x),BinaryRational.encode 0))
  else discardPrefix x

noncomputable def swapped (x : List Bool) : List Bool :=
  if eq (pairBits (discardPrefix x,extractPrefix (extractPrefix x))) then discardPrefix (extractPrefix x)
  else if eq (pairBits (discardPrefix x,discardPrefix (extractPrefix x))) then extractPrefix (extractPrefix x)
  else discardPrefix x
end MetricKMedianRecovery.BitMachine.BinaryLabel

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordExtras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordList RationalLeaves
noncomputable def missing (x : List Bool) : Bool := !contains (pairBits (discardPrefix x,extractPrefix x))
noncomputable def allIn (x : List Bool) : Bool := decide (Find.run missing x=[])
end MetricKMedianRecovery.BitMachine.BinaryLabel
namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordList RationalLeaves CanonicalMergeRefinement BinaryArithmetic
open BinaryFiniteContext (labels )
open BinaryOpeningPayment (field )
noncomputable def copied (x : List Bool) : List Bool := BinaryLabel.copied (pairBits (cf 2 x,jf 4 x))
noncomputable def labelsCheck (x : List Bool) : Bool :=
  if tagIs 1 x then BinaryLabel.allIn (pairBits (cf 0 x,jf 3 x)) else true

end MetricKMedianRecovery.BitMachine.BinaryJump

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
open WordList BinaryArithmetic

noncomputable def ranked (x : List Bool) : List Bool :=
  mapWith (fun y=>pairBits (discardPrefix (discardPrefix y),extractPrefix (discardPrefix y)))
    (pairBits ([],Zip.run (pairBits (Indices.run x,x))))
attribute [local irreducible] ranked
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n a : ℕ}
attribute [local irreducible] mapWith flatMapWith
noncomputable def parts (x : List Bool) : List Bool := flatMapWith partRow (pairBits (x,indices x))
end MetricKMedianRecovery.BitMachine.BinaryCopyTables

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingReference
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
attribute [local irreducible] WordList.mapWith
variable {n l : ℕ}
noncomputable def leaves (x : List Bool) : List Bool := mapWith leaf
  (pairBits (pairBits (field 0 x,field 4 x),Zip.run (pairBits (Indices.run (field 3 x),field 3 x))))
noncomputable def entries (x : List Bool) : List Bool := originals x++cons (pairBits (field 1 x,field 0 x)) (leaves x)
end MetricKMedianRecovery.BitMachine.BinarySamplingReference

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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {E : Type*} {a T : ℕ}
noncomputable def drawItems (x : List Bool) : List Bool := Zip.run (pairBits (Indices.run (field 1 x),field 1 x))
noncomputable def draw (x : List Bool) : List Bool := flatMapWith drawPick (pairBits (x,drawItems x))
noncomputable def advanceItem (x : List Bool) : List Bool :=
  Set.run (Set.pack (Lookup.run (pairBits (discardPrefix x,field 0 (extractPrefix x))))
    (field 2 (extractPrefix x)) (encode [Lookup.run (pairBits (discardPrefix x,field 1 (extractPrefix x)))]))
attribute [local irreducible] Set.run mapWith
noncomputable def advance (x : List Bool) : List Bool :=
  mapWith advanceItem (pairBits (x,Indices.run (field 1 x)))
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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q a T L : ℕ}
noncomputable def marginalDraw (x : List Bool) : List Bool :=
  draw (encode [field 1 (extractPrefix (extractPrefix x)),discardPrefix x,elementPart (extractPrefix x)])
noncomputable def marginal (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  BinaryRational.encode (BinaryRational.decode (g (pairBits (field 0 (extractPrefix (extractPrefix x)),
      cons (discardPrefix (extractPrefix x)) (marginalDraw x))))-
    BinaryRational.decode (g (pairBits (field 0 (extractPrefix (extractPrefix x)),marginalDraw x))))
noncomputable def marginalValues (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  mapWith (marginal g) (pairBits (x,elementSamples x))
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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )

attribute [local irreducible] mapWith
noncomputable def cap (x : List Bool) : List Bool :=
  RationalMin.run (cons (field 0 (discardPrefix x)) (offers x))
attribute [local irreducible] RationalMin.run
noncomputable def weightedCap (x : List Bool) : List Bool :=
  BinaryRational.encode (BinaryRational.decode (extractPrefix (discardPrefix x))*
    BinaryRational.decode (cap (pairBits (extractPrefix x,discardPrefix (discardPrefix x)))))
end MetricKMedianRecovery.BitMachine.BinaryCompletion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalBest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalBest
open WordList BinaryArithmetic
noncomputable def run (score : List Bool→List Bool) (x : List Bool) : List Bool :=
  CappedFold.run (choose score) (pairBits (x,Fold.pack (discardPrefix (discardPrefix x)) (extractPrefix x)
    (extractPrefix (discardPrefix x))))
noncomputable def fromList (score : List Bool→List Bool) (x : List Bool) : List Bool :=
  run score (pairBits (extractPrefix x,pairBits (head (discardPrefix x),tail (discardPrefix x))))
end MetricKMedianRecovery.BitMachine.BinaryRationalBest

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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
def pack (F S : Finset (Fin n)) (k : ℕ) (raw : List Bool) : List Bool :=
  encode [BinaryFinSet.encode F,BinaryFinSet.encode S,k.bits,raw]
end MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {A : Type*}
lemma value_choose (x y : Candidate A) : value (choose x y)=min (value x) (value y) := by
  cases x with
  | none=>simp [choose,value]
  | some x=>
    cases y with
    | none=>simp [choose,value]
    | some y=>
      dsimp [choose,value]
      split_ifs with h
      · apply (min_eq_left ?_).symm
        exact WithTop.coe_le_coe.mpr (by exact_mod_cast h)
      · apply (min_eq_right ?_).symm
        exact WithTop.coe_le_coe.mpr (by exact_mod_cast (le_of_not_ge h))
lemma choose_property (P : Candidate A→Prop) (x y : Candidate A) (hx : P x) (hy : P y) : P (choose x y) := by
  rcases choose_mem x y with h|h
  · rw [h];exact hx
  · rw [h];exact hy

lemma fold_property (P : Candidate A→Prop) (xs : List (Candidate A)) (s : Candidate A)
    (hs : P s) (hx : ∀ x∈xs,P x) : P (xs.foldl choose s) := by
  induction xs generalizing s with
  | nil=>exact hs
  | cons x xs ih=>exact ih (choose s x) (choose_property P s x hs (hx x (by simp))) (fun x h=>hx x (by simp [h]))
lemma fold_value (xs : List (Candidate A)) (s : Candidate A) :
    value (xs.foldl choose s)=min (value s) ((xs.map value).foldr min ⊤) := by
  induction xs generalizing s with
  | nil=>simp
  | cons x xs ih=>simp only [List.foldl_cons,ih,value_choose,List.map_cons,List.foldr_cons,min_assoc]
lemma select_value (xs : List (Candidate A)) : value (select xs)=((xs.map value).foldr min ⊤) := by
  unfold select
  rw [fold_value]
  change min ⊤ _=_
  exact min_top_left _
end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueDPValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {A L : Type*}
lemma value_merge (x y : Candidate (List A)) : value (merge x y)=value x+value y := by
  cases x with
  | none=>simp [merge,value]
  | some x=>
    cases y with
    | none=>simp [merge,value]
    | some y=>simp [merge,value,Rat.cast_add,WithTop.coe_add]
lemma value_collect (xs : List (Candidate (List A))) : value (collect xs)=(xs.map value).sum := by
  induction xs with
  | nil=>simp [collect,value]
  | cons x xs ih=>simpa only [collect,List.foldr_cons,value_merge,List.map_cons,List.sum_cons] using congrArg (value x+·) ih
lemma select_finset [DecidableEq L] (xs : List L) (f : L→Candidate A) :
    value (select (xs.map f))=xs.toFinset.inf (fun x=>value (f x)) := by
  rw [select_value,List.map_map]
  exact list_min_inf xs _

variable [LinearOrder L]
lemma recurrence_value (C : Finset L→Candidate (List A)) (t : ℕ) (U : Finset L) :
    value (recurrence C t U)=BlueSubsetDP.value (fun V=>value (C V)) t U := by
  induction t generalizing U with
  | zero=>by_cases h : U=∅ <;> simp [recurrence,BlueSubsetDP.value,h,value]
  | succ t ih=>
    rw [recurrence,select_finset,enumBlocks_set]
    simp only [value_merge,ih,BlueSubsetDP.value]
lemma best_value (C : Finset L→Candidate (List A)) (c : ℕ) (U : Finset L) :
    value (best C c U)=BlueSubsetDP.best (fun V=>value (C V)) c U := by
  by_cases h : U=∅
  · simp [best,BlueSubsetDP.best,h,value]
  · rw [best,ite_eq_right h,BlueSubsetDP.best,ite_eq_right h]
    have he : ((List.range c).map (fun t=>recurrence C (t+1) U))=
      (((List.range c).map (·+1)).map (fun t=>recurrence C t U)) := by simp
    rw [he,select_finset,range_succ_set]
    simp only [recurrence_value]
end MetricKMedianRecovery.BlueDP

namespace MetricKMedianRecovery.BlueDP
variable {L R Y : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder Y]
omit [LinearOrder Y] in
lemma item_value (B : Finset R) (label : R→L) (q : R→Y→ℚ) (l : L) (y : Y) :
    value (item B label q l y)=(B.filter (label ·=l)).inf (fun r=>((q r y:ℝ):WithTop ℝ)) := by
  rw [item,select_finset,Finset.sort_toFinset]
  rfl
omit [LinearOrder Y] in
lemma blockAt_value (B : Finset R) (label : R→L) (q : R→Y→ℚ) (U : Finset L) (y : Y) :
    value (blockAt B label q U y)=∑ l∈U,(B.filter (label ·=l)).inf (fun r=>((q r y:ℝ):WithTop ℝ)) := by
  rw [blockAt,value_collect,List.map_map]
  simp only [Function.comp_def,item_value]
  rw [←List.sum_toFinset _ (Finset.sort_nodup U (·≤·)),Finset.sort_toFinset]
lemma block_value (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (U : Finset L) :
    value (block B F label q U)=BlueSubsetDP.blockCost B F label (fun r y=>(q r y:ℝ)) U := by
  rw [block,select_finset,Finset.sort_toFinset]
  simp only [blockAt_value,BlueSubsetDP.blockCost]
lemma optimizer_value (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (c : ℕ) (U : Finset L) :
    value (best (block B F label q) c U)=BlueSubsetDP.best (BlueSubsetDP.blockCost B F label (fun r y=>(q r y:ℝ))) c U := by
  rw [best_value]
  simp only [block_value]
end MetricKMedianRecovery.BlueDP

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
open WordList
variable {A : Type*}
noncomputable def bad (x : List Bool) : List Bool := Find.run invalid (pairBits ([],x))
attribute [local irreducible] mapWith
noncomputable def contents (x : List Bool) : List Bool := flatMapWith payloadOp (pairBits ([],x))
noncomputable def result (x : List Bool) : List Bool := WordList.encode [pairBits (RationalArray.sumWords (scores x),contents x)]
noncomputable def run (x : List Bool) : List Bool := if bad x=[] then result x else []
end MetricKMedianRecovery.BitMachine.BinaryBlueCollect

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueBlocksMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueBlocks
open WordList
variable {L R : Type*} [LinearOrder L] [LinearOrder R] {n : ℕ}
noncomputable def atCenter (x : List Bool) : List Bool := BinaryBlueCollect.run (mapWith itemCall x)
noncomputable def atCall (x : List Bool) : List Bool := atCenter
  (pairBits (pairBits (extractPrefix (extractPrefix x),discardPrefix x),discardPrefix (extractPrefix x)))
noncomputable def run (x : List Bool) : List Bool := BinaryBlueChoice.select (mapWith atCall x)
end MetricKMedianRecovery.BitMachine.BinaryBlueBlocks

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueLookup
open WordList
variable {L A : Type*} [LinearOrder L]
noncomputable def run (x : List Bool) : List Bool := discardPrefix (List.tail (Find.run matchKey x))
end MetricKMedianRecovery.BitMachine.BinaryBlueLookup

namespace MetricKMedianRecovery.BitMachine.BinaryBlueCell
open WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ} {R : Type*} [LinearOrder R]
noncomputable def block (x : List Bool) : List Bool := BinaryBlueBlocks.run
  (pairBits (pairBits (field 0 (ctx x),discardPrefix x),field 1 (ctx x)))
end MetricKMedianRecovery.BitMachine.BinaryBlueCell

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueNextTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {L R Y : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder Y]
lemma select_spec {A : Type*} (P : Candidate A→Prop) (xs : List (Candidate A)) (h0 : P none)
    (hxs : ∀ x∈xs,P x) : P (select xs) := fold_property P xs none h0 hxs
lemma blockAt_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ)
    (U : Finset L) (y : Y) (hy : y∈F) : Spec B F label q U 1 (blockAt B label q U y) := by
  have hs:=collect_items_spec B F label q (U.sort (·≤·)) (Finset.sort_nodup U (·≤·)) y hy
  simp only [Finset.sort_toFinset,Finset.length_sort] at hs
  cases he : blockAt B label q U y with
  | none=>trivial
  | some v=>
    rcases v with ⟨k,xs⟩
    change Spec B F label q U U.card (blockAt B label q U y) at hs
    rw [he] at hs
    refine ⟨hs.1,hs.2.1,?_,hs.2.2.2⟩
    have hsub : destinations xs⊆{y} := by
      intro z hz
      obtain ⟨a,ha,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp hz)
      exact Finset.mem_singleton.mpr (collect_dest B label q (U.sort (·≤·)) y k xs he a ha)
    exact (Finset.card_le_card hsub).trans (by simp)
lemma block_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (U : Finset L) :
    Spec B F label q U 1 (block B F label q U) := by
  apply select_spec _ _ trivial
  intro x hx
  obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hx
  exact blockAt_spec B F label q U y ((Finset.mem_sort (·≤·)).mp hy)
end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BluePlan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {L R Y : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder Y]
omit [LinearOrder R] in
lemma spec_mono (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (U : Finset L)
    (c d : ℕ) (hcd : c≤d) (x : Candidate (List (Atom L R Y))) (hx : Spec B F label q U c x) : Spec B F label q U d x := by
  cases x with
  | none=>trivial
  | some x=>exact ⟨hx.1,hx.2.1,hx.2.2.1.trans hcd,hx.2.2.2⟩
lemma recurrence_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (t : ℕ) (U : Finset L) :
    Spec B F label q U t (recurrence (block B F label q) t U) := by
  induction t generalizing U with
  | zero=>
    rw [recurrence]
    split_ifs with h
    · subst U;exact empty_spec B F label q 0
    · trivial
  | succ t ih=>
    rw [recurrence]
    apply select_spec _ _ trivial
    intro x hx
    obtain ⟨V,hV,rfl⟩:=List.mem_map.mp hx
    have hVU := (BlueSubsetDP.mem_blocks.mp (enumBlocks_set U ▸ List.mem_toFinset.mpr hV)).2
    have hd : Disjoint V (U\V) := by
      apply Finset.disjoint_left.mpr
      intro l hl hrest
      exact (Finset.mem_sdiff.mp hrest).2 hl
    have hu : V∪(U\V)=U := by
      ext l
      simp only [Finset.mem_union,Finset.mem_sdiff]
      exact ⟨fun h=>h.elim (hVU ·) And.left,fun h=>by by_cases hV : l∈V;exact Or.inl hV;exact Or.inr ⟨h,hV⟩⟩
    have hh:=merge_spec B F label q V (U\V) 1 t _ _ (block_spec B F label q V) (ih (U\V)) hd
    simpa only [hu,Nat.add_comm 1] using hh
lemma best_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (c : ℕ) (U : Finset L) :
    Spec B F label q U c (best (block B F label q) c U) := by
  unfold best
  split_ifs with h
  · subst U;exact empty_spec B F label q c
  · apply select_spec _ _ trivial
    intro x hx
    obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hx
    exact spec_mono B F label q U (t+1) c (by have hh:=List.mem_range.mp ht;omega) _
      (recurrence_spec B F label q (t+1) U)
omit [LinearOrder R] [LinearOrder Y] in
lemma pick_mem (r0 : R) (y0 : Y) (xs : List (Atom L R Y)) (l : L) (hl : l∈(labels xs).toFinset) :
    pick r0 y0 xs l∈xs ∧ (pick r0 y0 xs l).1=l := by
  obtain ⟨a,ha,hal⟩:=List.mem_map.mp (List.mem_toFinset.mp hl)
  have hn : xs.find? (fun a=>a.1=l)≠none := by
    intro he
    exact List.find?_eq_none.mp he a ha (decide_eq_true hal)
  obtain ⟨b,hb⟩:=Option.ne_none_iff_exists'.mp hn
  simp only [pick,hb,Option.getD_some]
  exact ⟨List.mem_of_find?_eq_some hb,of_decide_eq_true (List.find?_some (p := fun a : Atom L R Y => decide (a.1=l)) hb)⟩
omit [LinearOrder R] [LinearOrder Y] in
lemma pick_eq (r0 : R) (y0 : Y) (xs : List (Atom L R Y)) (hn : (labels xs).Nodup)
    (a : Atom L R Y) (ha : a∈xs) : pick r0 y0 xs a.1=a := by
  have hp:=pick_mem r0 y0 xs a.1 (List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,ha,rfl⟩))
  exact List.inj_on_of_nodup_map hn hp.1 ha hp.2
omit [LinearOrder R] [LinearOrder Y] in
lemma cost_pick (r0 : R) (y0 : Y) (q : R→Y→ℚ) (xs : List (Atom L R Y)) (U : Finset L) (h : Route U xs) :
    (∑ l∈U,q (pick r0 y0 xs l).2.1 (pick r0 y0 xs l).2.2)=cost q xs := by
  rw [←h.2,List.sum_toFinset _ h.1]
  simp only [labels,List.map_map,Function.comp_def,cost]
  congr 1
  apply List.map_congr_left
  intro a ha
  rw [pick_eq r0 y0 xs h.1 a ha]
variable [Fintype L]
noncomputable def makePlan (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (c : ℕ)
    (r0 : R) (y0 : Y) (k : ℚ) (xs : List (Atom L R Y))
    (h : best (block B F label q) c Finset.univ=some (k,xs)) : BlueSubsetDP.Plan B F label (fun r y=>(q r y:ℝ)) c := by
  have hs:=best_spec B F label q c Finset.univ
  rw [h] at hs
  let sel : L→R := fun l=>(pick r0 y0 xs l).2.1
  let dst : L→Y := fun l=>(pick r0 y0 xs l).2.2
  have hp (l : L) := pick_mem r0 y0 xs l (hs.1.2 ▸ Finset.mem_univ l)
  have hv (l : L) : sel l∈B ∧ label (sel l)=l ∧ dst l∈F := by
    have hh:=hs.2.1 _ (hp l).1
    exact ⟨hh.1,hh.2.1.trans (hp l).2,hh.2.2⟩
  refine ⟨sel,dst,hv,?_,?_,?_⟩
  · intro l m he
    exact (hv l).2.1.symm.trans ((congrArg label he).trans (hv m).2.1)
  · apply (Finset.card_le_card ?_).trans hs.2.2.1
    intro y hy
    obtain ⟨l,_,rfl⟩:=Finset.mem_image.mp hy
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨_,(hp l).1,rfl⟩)
  · have hk : (∑ l,q (sel l) (dst l))=k := by
      simpa only [sel,dst] using (cost_pick r0 y0 q xs Finset.univ hs.1).trans hs.2.2.2.symm
    have hh:=optimizer_value B F label q c Finset.univ
    rw [h] at hh
    rw [←hh]
    change (((∑ l,(q (sel l) (dst l):ℝ)):ℝ):WithTop ℝ)=((k:ℝ):WithTop ℝ)
    rw [←Rat.cast_sum,hk]
end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchContext
open WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (label : Fin n→Fin m) (k c : ℕ) (extra : List Bool) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.encode D,BinaryFinSet.encode F,BinaryFinSet.encode S,
    BinaryRational.encode Δ,BinarySamplingState.encode s,BinaryFinSet.table colors,BinaryFinSet.table label,
    BinaryFinSet.table (id : Fin m→Fin m),k.bits,List.replicate c true,extra]
attribute [local irreducible] ballInput
end MetricKMedianRecovery.BitMachine.BinaryBranchContext

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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q p r : ℕ}
noncomputable def clientValues (x : List Bool) : List Bool :=
  mapWith cap (pairBits (discardPrefix x,field 1 (extractPrefix x)))
noncomputable def redValues (x : List Bool) : List Bool :=
  mapWith weightedCap (pairBits (discardPrefix x,field 2 (extractPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryCompletion

namespace MetricKMedianRecovery.BitMachine.BinaryBranchRows
open WordList
open BinaryOpeningPayment (field )
variable {n q r : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D S G : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (loc : Fin q→Fin n) (red : Fin r→Fin n) (k : ℕ) : List Bool :=
  encode [BinarySamplingOracle.pack δ D S Δ s,BinarySamplingOracle.pack δ D G Δ ⟨∅,s.leaves⟩,
    BinaryFinSet.table loc,BinaryFinSet.table red,k.bits]
end MetricKMedianRecovery.BitMachine.BinaryBranchRows

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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n q a p r b : ℕ}
attribute [local irreducible] fillInput
noncomputable def redValues (x : List Bool) : List Bool := BinaryCompletion.redValues (pairBits (field 10 x,field 9 x))
attribute [local irreducible] redValues
end MetricKMedianRecovery.BitMachine.BinaryCompletionRealize

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchObjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryObservableBranch
open WordList BinaryBranchContext BinaryBranchProgram
open BinaryOpeningPayment (field )
variable {n m : ℕ}
noncomputable def output (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
    (s : RationalSampling.State n) (colors : Fin n→Fin 3) (label : Fin n→Fin m) (q c : ℕ) (r0 y0 : Fin n)
    (bits : Categorical.BinaryOracleIndex (Fin (s.leaves.length*n)) s.leaves.length (Categorical.Explicit.exponent s.leaves.length)
      (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length)→Bool) : Finset (Fin n) := by
  classical
  exact if hr : BinaryBranchCheck.Ready δ F S s colors q c m then
    match hb : BlueDP.best (BlueDP.block ((S\s.deleted).filter (fun i=>colors i=2)) F label (rationalScore δ D S Δ s)) c Finset.univ with
    | none=>S
    | some (v,xs)=>
      let P:=BlueDP.makePlan _ _ _ _ _ r0 y0 v xs hb
      result δ D F S Δ s colors hr.2.1 P.sel P.dst q bits
  else S
end MetricKMedianRecovery.BitMachine.BinaryObservableBranch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_FavorableReady
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryObservableBranch
open Completion Categorical FiniteSampling BinaryBranchContext Sampling BinaryBranchProgram
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
abbrev Bits (n p : ℕ) := Categorical.BinaryOracleIndex (Fin (p*n)) p (Categorical.Explicit.exponent p)
  (Categorical.Explicit.samples (p*n) p)→Bool
end MetricKMedianRecovery.BitMachine.BinaryObservableBranch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchSeedLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchTape
open BinarySeed BinaryObservableBranch
abbrev completionCount (n p : ℕ) :=
  BinaryCategorical.Tape.M (p*n) p (Categorical.Explicit.exponent p) (Categorical.Explicit.samples (p*n) p)+
    BinaryCategorical.Tape.K p (Categorical.Explicit.exponent p)
abbrev count (n b p : ℕ) := (colorCount n+labelCount n b)+completionCount n p
abbrev Seed (n b p : ℕ) := ((Fin n→Fin 4)×(Fin n→Fin (ColorLabel.labelRange b)))×Bits n p
def layout (n b p : ℕ) : (Fin (count n b p)→Bool)≃Seed n b p :=
  (split (colorCount n+labelCount n b) (completionCount n p)).trans
    (Equiv.prodCongr ((split (colorCount n) (labelCount n b)).trans
      (Equiv.prodCongr (colors n) (labels n b)))
      (BinaryCategorical.Tape.layout (p*n) p (Categorical.Explicit.exponent p) (Categorical.Explicit.samples (p*n) p)))
def raw {n b p : ℕ} (s : Seed n b p) : List Bool :=
  (BinarySeed.raw (colorTensor s.1.1)++BinarySeed.raw (labelTensor s.1.2))++
    BinaryCategorical.Tape.raw (p*n) p (Categorical.Explicit.exponent p) (Categorical.Explicit.samples (p*n) p) s.2
end MetricKMedianRecovery.BitMachine.BinaryBranchTape

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
open WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels )
noncomputable def applyWord (x : List Bool) : List Bool :=
  if extractPrefix x=[] then discardPrefix x else BinaryLabel.swapped x
noncomputable def mapRow : List Bool→List Bool := mapWith applyWord
noncomputable def mapHistory : List Bool→List Bool := mapWith mapRow
end MetricKMedianRecovery.BitMachine.BinaryCorrection

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels )
noncomputable def mapPrefix (x : List Bool) : List Bool := BinaryCorrection.mapHistory (pairBits (field 2 x,field 1 x))
attribute [local irreducible] BinaryCorrection.mapHistory
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
open WordList RationalLeaves BinaryArithmetic
noncomputable def containsItem (x : List Bool) : Bool := BinaryLabel.contains (pairBits (discardPrefix x,extractPrefix x))
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

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
open WordList RationalLeaves CanonicalMergeRefinement
open BinaryFiniteContext (labels )
open BinaryOpeningPayment (field )
noncomputable def spareWord (x : List Bool) : List Bool := BinaryLabel.copied (pairBits (cf 0 x,jf 4 x))
end MetricKMedianRecovery.BitMachine.BinaryJump

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
open WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels )
noncomputable def mappedPrefix (x : List Bool) : List Bool := BinaryCoupled.mapPrefix (field 6 x)
noncomputable def prefixG (x : List Bool) : List Bool := mappedPrefix x++cons (G x) []
end MetricKMedianRecovery.BitMachine.BinaryCoupledStep

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
open WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels )

noncomputable def loInput (x : List Bool) : List Bool := pairBits (ctx x,field 5 x)

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
open WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field )
open BinaryFiniteContext (labels )
variable {m d : ℕ}
def pack (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m)) (M : ℚ) (k : ℕ) : List Bool :=
  encode [Rectangular.encode distance,List.replicate d true,BinaryFinSet.encode F,
    encode (List.ofFn (fun j=>(loc j).val.bits)),BinaryRational.encode M,k.bits]
end MetricKMedianRecovery.BitMachine.BinaryInitialAuto

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
open WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )
variable {m : ℕ}
def pack (δ : Fin m→Fin m→ℕ) (F D : Finset (Fin m)) (M h L : ℕ) : List Bool :=
  pairBits (BinaryInitialAuto.pack (fun i j=>(δ (SortedIndex.enum D j) i:ℚ))
    (SortedIndex.enum D) F (M:ℚ) h,(h+L).bits)
end MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus

end OAI
end


