-- Prove2me | Definitions.Def_Q238K011
-- name    : Q238K011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:13:42.150196+00:00
-- url     : https://prove2.me/theorems/d6613578-c02c-4020-9243-f6e52aa4d25a
-- title:
--   Definitions bundle Q238K011 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 67 declarations of OpenAI's Lean: 48 definitions and 19 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.cshape`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.nword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.dimensions`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.pword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.qword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.aword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.dimensions`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.qword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.bagTest`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.context`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.drawPick`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.drawRow`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.elementPart`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.elementSamples`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.initial`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.rule`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.stepScore`, `OAI.MetricKMedianRecovery.BitMachine.BinaryColorLabel.colorWord`, `OAI.MetricKMedianRecovery.BitMachine.BinaryColorLabel.labelOp`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.look`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.offers`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm.choices`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.context`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFill.test`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.fillInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.ctx`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalBest.choose`, `OAI.MetricKMedianRecovery.BitMachine.BinarySeed.indices`, `OAI.MetricKMedianRecovery.BitMachine.BinarySeed.normalizeBig`, `OAI.MetricKMedianRecovery.BitMachine.WordList.Drop.run`, `OAI.MetricKMedianRecovery.BlueDP.Route`, `OAI.MetricKMedianRecovery.BlueDP.Spec`, `OAI.MetricKMedianRecovery.BlueDP.Valid`, `OAI.MetricKMedianRecovery.BlueDP.best`, `OAI.MetricKMedianRecovery.BlueDP.block`, `OAI.MetricKMedianRecovery.BlueDP.blockAt`, `OAI.MetricKMedianRecovery.BlueDP.choose`, `OAI.MetricKMedianRecovery.BlueDP.collect` and 8 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_CompletionAlgorithm`, `KMedianRecovery_Branching_BlueChoice`, `KMedianRecovery_Branching_BlueDPValue`, `KMedianRecovery_Branching_BlueNextTable`, `KMedianRecovery_Branching_BranchSeedLayout`, `KMedianRecovery_Branching_CategoricalChoice`, `KMedianRecovery_Branching_CategoricalRawPrep`, `KMedianRecovery_Branching_CategoricalScore`, `KMedianRecovery_Branching_CategoricalSize`, `KMedianRecovery_Branching_CategoricalTable`, `KMedianRecovery_Branching_CompletionFair`, `KMedianRecovery_Branching_CompletionRealize`, `KMedianRecovery_Branching_CopyGround`, `KMedianRecovery_Branching_RandomizedZeroBranch`, `KMedianRecovery_Branching_RationalBranch`, `KMedianRecovery_Encoding_ColorLabelMachine`, `KMedianRecovery_Encoding_RationalBest`, `KMedianRecovery_Encoding_RationalCap`, `KMedianRecovery_Encoding_UniformWord`, `KMedianRecovery_Encoding_WordExtras`, `KMedianRecovery_Machines_InitialLoop`, `KMedianRecovery_Recovery_OrderedMaximum`, `KMedianRecovery_Recovery_RawUnary`, `KMedianRecovery_Sampling_SeedTensor`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K000`, `Q238K001`, `Q238K002` and `Q238K003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K020`, `Q238K021` and `Q238K022`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result_guarantee_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result_guarantee_s238`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm.sixtyTwoFin_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result_guarantee_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K000
import Definitions.Def_Q238K001
import Definitions.Def_Q238K002
import Definitions.Def_Q238K003

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
noncomputable def drawRow (x : List Bool) : List Bool :=
  Lookup.run (pairBits (extractPrefix (discardPrefix x),field 0 (extractPrefix x)))
noncomputable def drawPick (x : List Bool) : List Bool :=
  if value (extractPrefix (discardPrefix x))=value (field 2 (extractPrefix x)) then []
  else Lookup.run (pairBits (discardPrefix (discardPrefix x),drawRow x))
attribute [local irreducible] mapWith
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
noncomputable def elementPart (x : List Bool) : List Bool :=
  Lookup.run (pairBits (discardPrefix x,field 3 (extractPrefix x)))
noncomputable def elementSamples (x : List Bool) : List Bool :=
  Lookup.run (pairBits (discardPrefix x,field 2 (extractPrefix x)))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_OrderedMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.OrderedMaximum
variable {E β : Type*} [LinearOrder β]
lemma mem (score : E→β) (s : E) (as : List E) : run score s as=s ∨ run score s as∈as := by
  induction as generalizing s with
  | nil=>exact Or.inl rfl
  | cons a as ih=>
    unfold run
    rcases ih (if score s < score a then a else s) with h|h
    · by_cases hs : score s < score a
      · simp only [ite_eq_left hs] at h
        simpa only [ite_eq_left hs] using Or.inr (List.mem_cons.mpr (Or.inl h))
      · simpa only [ite_eq_right hs] using Or.inl h
    · exact Or.inr (List.mem_cons.mpr (Or.inr h))
lemma own_le (score : E→β) (s : E) (as : List E) : score s ≤ score (run score s as) := by
  induction as generalizing s with
  | nil=>exact le_rfl
  | cons a as ih=>
    unfold run
    by_cases hs : score s < score a
    · rw [ite_eq_left hs]
      exact hs.le.trans (ih a)
    · rw [ite_eq_right hs]
      exact ih s
lemma score_le (score : E→β) (s : E) (as : List E) (a : E) (ha : a∈as) : score a ≤ score (run score s as) := by
  induction as generalizing s with
  | nil=>exact False.elim (List.not_mem_nil ha)
  | cons b as ih=>
    unfold run
    rcases List.mem_cons.mp ha with rfl|ha
    · by_cases hs : score s < score a
      · rw [ite_eq_left hs]; exact own_le score a as
      · rw [ite_eq_right hs]; exact (le_of_not_gt hs).trans (own_le score s as)
    · exact ih (if score s < score b then b else s) ha
lemma ofList_mem (score : E→β) (as : List E) (h : as≠[]) : ofList score as h∈as := by
  rcases mem score (as.head h) as.tail with he|he
  · rw [ofList,he]
    exact List.head_mem h
  · exact List.mem_of_mem_tail he
lemma le_ofList (score : E→β) (as : List E) (h : as≠[]) (a : E) (ha : a∈as) :
    score a ≤ score (ofList score as h) := by
  cases as with
  | nil=>exact False.elim (h rfl)
  | cons b as=>
    rcases List.mem_cons.mp ha with rfl|ha
    · exact own_le score a as
    · exact score_le score b as a ha
end MetricKMedianRecovery.OrderedMaximum

namespace MetricKMedianRecovery.Categorical.Selected
variable {E : Type*} [DecidableEq E] {a : ℕ}
noncomputable def orderedRule (es : List E) (he : ∀ e,e∈es) (part : E→Fin a)
    (hp : Function.Surjective part) : Rule part where
  choose score j:=OrderedMaximum.ofList score (bag es part j) (bag_ne_nil es he part hp j)
  spec score j:=by
    have hm := OrderedMaximum.ofList_mem score (bag es part j) (bag_ne_nil es he part hp j)
    refine ⟨by exact of_decide_eq_true (List.mem_filter.mp hm).2,?_⟩
    intro e hpart
    exact OrderedMaximum.le_ofList score (bag es part j) (bag_ne_nil es he part hp j) e
      (List.mem_filter.mpr ⟨he e,by simpa only [decide_eq_true_eq] using hpart⟩)
end MetricKMedianRecovery.Categorical.Selected

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
noncomputable def choose (score : List Bool→List Bool) (x : List Bool) : List Bool :=
  if BinaryRational.decode (score (pairBits (Find.context x,Fold.accum x))) <
      BinaryRational.decode (score (pairBits (Find.context x,Find.item x)))
  then Find.item x else Fold.accum x
end MetricKMedianRecovery.BitMachine.BinaryRationalBest

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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q a T L : ℕ}
noncomputable def rule (part : Fin q→Fin a) (hp : Function.Surjective part) : Categorical.Selected.Rule part :=
  Categorical.Selected.orderedRule (elements q) mem_elements part hp
noncomputable def bagTest (x : List Bool) : Bool :=
  decide (value (elementPart (pairBits (extractPrefix (extractPrefix x),discardPrefix x)))=
    value (discardPrefix (extractPrefix x)))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryCategorical

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q a T L : ℕ}
noncomputable def stepScore (x : List Bool) : List Bool :=
  encode [field 0 (Find.context x),field 1 (Fold.accum x),Find.item x,field 1 (Find.context x)]
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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q a T L : ℕ}
noncomputable def initial (x : List Bool) : List Bool :=
  encode [[],repeatWords (pairBits (field 2 x,repeatWords (pairBits (field 3 x,[]))))]
noncomputable def context (x : List Bool) : List Bool := encode [field 0 x,field 1 x,field 3 x]
end MetricKMedianRecovery.BitMachine.BinaryCategorical

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
lemma copies_singleton (n : ℕ) (b : Bool) : RepeatedAppend.copies n [b]=List.replicate n b := by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [RepeatedAppend.copies,ih,List.replicate_succ']
end MetricKMedianRecovery.BitMachine.RawUnary

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordExtras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic
namespace WordList
namespace Drop
open Lookup (step )
def run (x : List Bool) : List Bool := discardPrefix (step^[x.length] x)
end Drop
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_UniformWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
open BinaryArithmetic
noncomputable def normalizeBig (x : List Bool) : List Bool := BinaryArithmetic.normalize x.reverse
end MetricKMedianRecovery.BitMachine.BinarySeed

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
open WordList BinaryArithmetic
noncomputable def indices (x : List Bool) : List Bool := BinaryEllipsoidInitial.indices (head (extractPrefix x))
end MetricKMedianRecovery.BitMachine.BinarySeed

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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
open Categorical.Explicit
variable {q a : ℕ}
noncomputable def qword (x : List Bool) : List Bool := Count.run (field 1 (extractPrefix x))
noncomputable def aword (x : List Bool) : List Bool := field 2 (extractPrefix x)
noncomputable def dimensions (x : List Bool) : List Bool := pairBits (qword x,aword x)
attribute [local irreducible] dimensions
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionFill
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q a : ℕ}
noncomputable def test (x : List Bool) : Bool :=
  decide (value (Lookup.run (pairBits (discardPrefix x,field 0 (extractPrefix x))))=value (field 1 (extractPrefix x)))
end MetricKMedianRecovery.BitMachine.BinaryCompletionFill

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
open WordList BinaryArithmetic
attribute [local irreducible] WordList.mapWith
noncomputable def colorWord (x : List Bool) : List Bool :=
  if value x<2 then (0:ℕ).bits else if value x=2 then (1:ℕ).bits else (2:ℕ).bits
noncomputable def labelOp (x : List Bool) : List Bool := (value (discardPrefix x)%value (extractPrefix x)).bits
end MetricKMedianRecovery.BitMachine.BinaryColorLabel

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

noncomputable def look (x : List Bool) : List Bool := Lookup.run (pairBits (discardPrefix x,extractPrefix x))
noncomputable def offers (x : List Bool) : List Bool :=
  mapWith look (pairBits (field 1 (discardPrefix x),extractPrefix x))
attribute [local irreducible] mapWith
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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n q a p r b : ℕ}
noncomputable def fillInput (x : List Bool) : List Bool := encode [field 3 x,field 4 x,field 9 x]
attribute [local irreducible] fillInput
end MetricKMedianRecovery.BitMachine.BinaryCompletionRealize

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_CompletionAlgorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm
open WordList BinaryArithmetic
variable {n q a p r b T L : ℕ}
noncomputable def choices (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ)
    (part : Fin q→Fin a) (hp : Function.Surjective part)
    (seed : (Fin T→Categorical.OracleSeed (Fin q) a T L)×(Fin a→Fin T)) : List (Fin q) :=
  BinaryCategorical.drawn (Categorical.Selected.greedyRun part (BinaryCategorical.rule part hp)
    (fun S=>(BinaryCompletion.savingQ k base distance weight redBase redDistance S:ℝ)) seed.1).2 seed.2
end MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm

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
def choose : Candidate A→Candidate A→Candidate A
  | none,y=>y
  | x,none=>x
  | some x,some y=>if x.1≤y.1 then some x else some y
lemma choose_mem (x y : Candidate A) : choose x y=x ∨ choose x y=y := by
  cases x <;> cases y <;> simp only [choose]
  all_goals first | exact Or.inl trivial | exact Or.inr trivial | (split_ifs <;> simp)

def select (xs : List (Candidate A)) : Candidate A := xs.foldl choose none
lemma fold_mem (xs : List (Candidate A)) (s : Candidate A) : xs.foldl choose s=s ∨ xs.foldl choose s∈xs := by
  induction xs generalizing s with
  | nil=>simp
  | cons x xs ih=>
    rw [List.foldl_cons]
    rcases ih (choose s x) with h|h
    · rcases choose_mem s x with he|he
      · exact Or.inl (h.trans he)
      · exact Or.inr (List.mem_cons.mpr (Or.inl (h.trans he)))
    · exact Or.inr (List.mem_cons_of_mem _ h)
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
def merge : Candidate (List A)→Candidate (List A)→Candidate (List A)
  | some (q,x),some (r,y)=>some (q+r,x++y)
  | _,_=>none
def collect (xs : List (Candidate (List A))) : Candidate (List A) := xs.foldr merge (some (0,[]))

variable [LinearOrder L]

def recurrence (C : Finset L→Candidate (List A)) : ℕ→Finset L→Candidate (List A)
  | 0,U=>if U=∅ then some (0,[]) else none
  | t+1,U=>select ((enumBlocks U).map (fun V=>merge (C V) (recurrence C t (U\V))))
def best (C : Finset L→Candidate (List A)) (c : ℕ) (U : Finset L) : Candidate (List A) :=
  if U=∅ then some (0,[]) else select ((List.range c).map (fun t=>recurrence C (t+1) U))
end MetricKMedianRecovery.BlueDP

namespace MetricKMedianRecovery.BlueDP
variable {L R Y : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder Y]

def item (B : Finset R) (label : R→L) (q : R→Y→ℚ) (l : L) (y : Y) : Candidate (List (Atom L R Y)) :=
  select (((B.filter (label ·=l)).sort (·≤·)).map (fun r=>some (q r y,[(l,r,y)])))
def blockAt (B : Finset R) (label : R→L) (q : R→Y→ℚ) (U : Finset L) (y : Y) : Candidate (List (Atom L R Y)) :=
  collect ((U.sort (·≤·)).map (fun l=>item B label q l y))
def block (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (U : Finset L) : Candidate (List (Atom L R Y)) :=
  select ((F.sort (·≤·)).map (blockAt B label q U))
end MetricKMedianRecovery.BlueDP

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
def labels (xs : List (Atom L R Y)) : List L := xs.map Prod.fst
def destinations (xs : List (Atom L R Y)) : Finset Y := (xs.map (fun a=>a.2.2)).toFinset
def cost (q : R→Y→ℚ) (xs : List (Atom L R Y)) : ℚ := (xs.map (fun a=>q a.2.1 a.2.2)).sum
def Valid (B : Finset R) (F : Finset Y) (label : R→L) (xs : List (Atom L R Y)) : Prop :=
  ∀ a∈xs,a.2.1∈B ∧ label a.2.1=a.1 ∧ a.2.2∈F
def Route (U : Finset L) (xs : List (Atom L R Y)) : Prop := (labels xs).Nodup ∧ (labels xs).toFinset=U
def Spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ)
    (U : Finset L) (c : ℕ) : Candidate (List (Atom L R Y))→Prop
  | none=>True
  | some (k,xs)=>Route U xs ∧ Valid B F label xs ∧ (destinations xs).card ≤ c ∧ k=cost q xs
omit [LinearOrder R] [LinearOrder Y] in
lemma route_append (U V : Finset L) (xs ys : List (Atom L R Y)) (hx : Route U xs) (hy : Route V ys)
    (hUV : Disjoint U V) : Route (U∪V) (xs++ys) := by
  rcases hx with ⟨hxn,hx⟩
  rcases hy with ⟨hyn,hy⟩
  refine ⟨?_,?_⟩
  · rw [labels,List.map_append,List.nodup_append]
    refine ⟨hxn,hyn,?_⟩
    intro a hax b hay hab
    subst b
    exact (Finset.disjoint_left.mp hUV (hx ▸ List.mem_toFinset.mpr hax) (hy ▸ List.mem_toFinset.mpr hay))
  · simp only [labels,List.map_append,List.toFinset_append] at hx hy ⊢
    rw [hx,hy]
omit [LinearOrder L] [LinearOrder R] [LinearOrder Y] in
lemma valid_append (B : Finset R) (F : Finset Y) (label : R→L) (xs ys : List (Atom L R Y))
    (hx : Valid B F label xs) (hy : Valid B F label ys) : Valid B F label (xs++ys) := by
  intro a ha
  rcases List.mem_append.mp ha with h|h
  · exact hx a h
  · exact hy a h
omit [LinearOrder R] in
lemma merge_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ)
    (U V : Finset L) (c d : ℕ) (x y : Candidate (List (Atom L R Y)))
    (hx : Spec B F label q U c x) (hy : Spec B F label q V d y) (hUV : Disjoint U V) :
    Spec B F label q (U∪V) (c+d) (merge x y) := by
  cases x with
  | none=>trivial
  | some x=>
    cases y with
    | none=>trivial
    | some y=>
      rcases x with ⟨k,xs⟩
      rcases y with ⟨j,ys⟩
      rcases hx with ⟨hx,hxv,hxc,rfl⟩
      rcases hy with ⟨hy,hyv,hyc,rfl⟩
      refine ⟨route_append U V xs ys hx hy hUV,valid_append B F label xs ys hxv hyv,?_,?_⟩
      · simp only [destinations,List.map_append,List.toFinset_append]
        exact (Finset.card_union_le _ _).trans (Nat.add_le_add hxc hyc)
      · simp [cost,List.sum_append]
omit [LinearOrder R] in
lemma empty_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (c : ℕ) :
    Spec B F label q ∅ c (some (0,[])) := by
  simp [Spec,Route,labels,Valid,destinations,cost]
omit [LinearOrder Y] in
lemma item_witness (B : Finset R) (label : R→L) (q : R→Y→ℚ) (l : L) (y : Y)
    (k : ℚ) (xs : List (Atom L R Y)) (h : item B label q l y=some (k,xs)) :
    ∃ r∈B,label r=l ∧ k=q r y ∧ xs=[(l,r,y)] := by
  have hh:=fold_mem (((B.filter (label ·=l)).sort (·≤·)).map (fun r=>some (q r y,[(l,r,y)]))) none
  change item B label q l y=none ∨ item B label q l y∈_ at hh
  rcases hh with he|hm
  · rw [h] at he;cases he
  · rw [h] at hm
    obtain ⟨r,hr,he⟩:=List.mem_map.mp hm
    have hr':=Finset.mem_filter.mp ((Finset.mem_sort (·≤·)).mp hr)
    have he':=Option.some.inj he
    exact ⟨r,hr'.1,hr'.2,(congrArg Prod.fst he').symm,(congrArg Prod.snd he').symm⟩
lemma item_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (l : L) (y : Y) (hy : y∈F) :
    Spec B F label q {l} 1 (item B label q l y) := by
  cases he : item B label q l y with
  | none=>trivial
  | some x=>
    rcases x with ⟨k,xs⟩
    obtain ⟨r,hr,hlabel,rfl,rfl⟩:=item_witness B label q l y k xs he
    simp [Spec,Route,labels,Valid,destinations,cost,hr,hlabel,hy]
lemma collect_items_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ)
    (ls : List L) (hls : ls.Nodup) (y : Y) (hy : y∈F) :
    Spec B F label q ls.toFinset ls.length (collect (ls.map (fun l=>item B label q l y))) := by
  induction ls with
  | nil=>exact empty_spec B F label q 0
  | cons l ls ih=>
    have hls':=List.nodup_cons.mp hls
    have hh:=merge_spec B F label q {l} ls.toFinset 1 ls.length _ _ (item_spec B F label q l y hy) (ih hls'.2)
      (by simpa using hls'.1)
    simpa only [List.map_cons,collect,List.foldr_cons,List.toFinset_cons,List.length_cons,
      Finset.singleton_union,Nat.add_comm 1] using hh
omit [LinearOrder Y] in
lemma collect_dest (B : Finset R) (label : R→L) (q : R→Y→ℚ) (ls : List L) (y : Y)
    (k : ℚ) (xs : List (Atom L R Y)) (h : collect (ls.map (fun l=>item B label q l y))=some (k,xs)) :
    ∀ a∈xs,a.2.2=y := by
  induction ls generalizing k xs with
  | nil=>simp only [List.map_nil,collect,List.foldr_nil,Option.some.injEq,Prod.mk.injEq] at h;rw [←h.2];simp
  | cons l ls ih=>
    change merge (item B label q l y) (collect (ls.map (fun l=>item B label q l y)))=some (k,xs) at h
    cases hi : item B label q l y with
    | none=>simp [hi,merge] at h
    | some v=>
      rcases v with ⟨j,ys⟩
      obtain ⟨r,_,_,rfl,rfl⟩:=item_witness B label q l y j ys hi
      cases ht : collect (ls.map (fun l=>item B label q l y)) with
      | none=>simp [hi,ht,merge] at h
      | some v=>
        rcases v with ⟨z,zs⟩
        rw [hi,ht,merge] at h
        have he:=congrArg Prod.snd (Option.some.inj h)
        dsimp only at he
        rw [←he]
        intro a ha
        rcases List.mem_append.mp ha with ha|ha
        · simpa using (List.mem_singleton.mp ha ▸ rfl : a.2.2=y)
        · exact ih z zs ht a ha
end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyGround
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion.CopyGround
variable {n a : ℕ}
lemma part_embed (H : Fin a→Finset (Fin n)) (e : (i : Fin a)×(H i)) : part (embed H e)=e.1 := by
  exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (e.1,e.2.val))
lemma part_origin (H : Fin a→Finset (Fin n)) (hH : ∀ i,(H i).Nonempty) (i : Fin a) : part (origin H hH i)=i :=
  part_embed H _
lemma part_surjective (H : Fin a→Finset (Fin n)) (hH : ∀ i,(H i).Nonempty) : Function.Surjective (part (n:=n) (a:=a)) :=
  fun i=>⟨origin H hH i,part_origin H hH i⟩
end MetricKMedianRecovery.Completion.CopyGround

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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
open Categorical.Explicit
variable {n q a p r c : ℕ}
noncomputable def context (x : List Bool) : List Bool := encode
  [field 10 (extractPrefix x),field 3 (extractPrefix x),Count.run (field 4 (extractPrefix x))]
section Correct
variable (F S Q : Finset (Fin n)) (part : Fin q→Fin a) (hp : Function.Surjective part)
    (o : Fin a→Fin q) (loc : Fin q→Fin n) (redLoc : Fin r→Fin n) (blueLoc blueDest : Fin c→Fin n)
    (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ)
noncomputable def result
    (bits : Categorical.BinaryOracleIndex (Fin q) a (exponent a) (samples q a)→Bool) : Finset (Fin n) :=
  let xs:=BinaryCompletionAlgorithm.choices k base distance weight redBase redDistance part hp
    (Categorical.binarySeedEquiv (Fin q) a (exponent a) (samples q a) bits)
  Completion.Canonical.realize F S Q part o loc redLoc blueLoc blueDest xs
    (BinaryRationalSort.indexSet (fun i=>weight i*BinaryCompletion.capped (redBase i) (redDistance i) xs.toFinset) k)
end Correct
end MetricKMedianRecovery.BitMachine.BinaryCompletionFair

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RationalBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open Completion Categorical FiniteSampling BinaryBranchContext
variable {n m : ℕ}
noncomputable def result (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (hH : ∀ i,(balls δ F s i).Nonempty) (sel dest : Fin m→Fin n) (k : ℕ)
    (bits : BinaryOracleIndex (Fin (s.leaves.length*n)) s.leaves.length (Explicit.exponent s.leaves.length)
      (Explicit.samples (s.leaves.length*n) s.leaves.length)→Bool) : Finset (Fin n) :=
  let red:=(S\s.deleted).filter (fun i=>colors i=1)
  let green:=(S\s.deleted).filter (fun i=>colors i=0)
  let loc:=CopyGround.location (balls δ F s) hH
  BinaryCompletionFair.result F S s.deleted CopyGround.part (CopyGround.part_surjective (balls δ F s) hH)
    (CopyGround.origin (balls δ F s) hH) loc (SortedIndex.enum red) sel dest k
    (fun i=>RationalSampling.reference δ S Δ s (SortedIndex.enum D i))
    (fun i e=>δ (SortedIndex.enum D i) (loc e))
    (fun i=>RationalSampling.assignmentWeight δ D S Δ s (SortedIndex.enum red i))
    (fun i=>RationalSampling.reference δ green Δ ⟨∅,s.leaves⟩ (SortedIndex.enum red i))
    (fun i e=>δ (SortedIndex.enum red i) (loc e)) bits
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

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
open WordList BinaryArithmetic BinaryBranchContext
open BinaryOpeningPayment (field )
attribute [local irreducible] Count.run 
noncomputable def nword (x : List Bool) : List Bool := Count.run (field 0 x)
noncomputable def cshape (x : List Bool) : List Bool := encode [nword x,[true,true]]
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
open WordList BinaryArithmetic BinaryBranchContext
open BinaryOpeningPayment (field )
open BinaryCategorical
noncomputable def pword (x : List Bool) : List Bool := Count.run (discardPrefix (field 5 x))
noncomputable def qword (x : List Bool) : List Bool := RepeatedAppend.copies (pword x).length (BinaryBranchRandomize.nword x)
noncomputable def dimensions (x : List Bool) : List Bool := pairBits (qword x,pword x)
attribute [local irreducible] dimensions
end MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count

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
noncomputable def ctx (x : List Bool) : List Bool := pairBits (field 3 x,field 0 x)

end MetricKMedianRecovery.BitMachine.BinaryInitial

end OAI
end


