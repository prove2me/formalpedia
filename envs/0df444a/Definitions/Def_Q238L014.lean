-- Prove2me | Definitions.Def_Q238L014
-- name    : Q238L014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:22:56.355344+00:00
-- url     : https://prove2.me/theorems/ee9ae76a-e350-4a19-a59c-7e424ebd93f6
-- title:
--   Definitions bundle Q238L014 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 234 declarations of OpenAI's Lean: 220 definitions and 14 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.boundWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.coeffWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.denOp`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.denominator`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.denominators`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.entries`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.scalar`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.bound`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.boundOp`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.boxShape`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.boxWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.relaxedOp`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.center`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.cutInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.dim`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.direction`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.found`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.nextState`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.normWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.precision`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.rest`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.rest₂`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.rows`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.shape`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.stored`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.updated`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.zeroDirection`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.center`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.centerInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.centerWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.coefA`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.coefB`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.coefCenter`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.coefInflate`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.cutInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.cutWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.difference`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.differenceInput` and 180 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_CopyComputes`, `KMedianRecovery_Encoding_Encode2`, `KMedianRecovery_Encoding_Encode3`, `KMedianRecovery_Encoding_OptionEncode`, `KMedianRecovery_Machines_LoopInput2`, `KMedianRecovery_Recovery_BoundOp`, `KMedianRecovery_Recovery_BoundedDecision`, `KMedianRecovery_Recovery_FaceSelection`, `KMedianRecovery_Recovery_GetRow2`, `KMedianRecovery_Recovery_LeftNum`, `KMedianRecovery_Recovery_MulComputes`, `KMedianRecovery_Recovery_NumAbs`, `KMedianRecovery_Recovery_Op`, `KMedianRecovery_Recovery_Pack3`, `KMedianRecovery_Recovery_Pack4`, `KMedianRecovery_Recovery_Pack5`, `KMedianRecovery_Recovery_Pack6`, `KMedianRecovery_Recovery_Pack7`, `KMedianRecovery_Recovery_Pack8`, `KMedianRecovery_Recovery_Pack9`, `KMedianRecovery_Recovery_ProcessOutputs`, `KMedianRecovery_Recovery_Rectangular`, `KMedianRecovery_Recovery_StepThen`, `KMedianRecovery_Recovery_Store2`, `KMedianRecovery_Sampling_ExtractPrefix`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundle `Q238L006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L022`, `Q238L023`, `Q238L024`, `Q238L025` and `Q238L026`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L006

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_StepThen
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_left _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_one _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_zero _root_.OAI.MetricKMedianRecovery.BitMachine.discardPrefix_pairBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

abbrev tailProgram : Program where
  K := Unit
  input := ()
  output := ()
  Label := Unit
  main := ()
  State := Option Bool
  initial := none
  code _ := .pop () (fun _ b => b)
    (.branch (fun s => decide (s = some true))
      (.pop () (fun _ _ => none) (.goto (fun _ => ())))
      (.load (fun _ => none) .halt))

def tailCfg (xs : List Bool) : tailProgram.machine.Cfg := ⟨some (),none,fun _ => xs⟩
def tailEnd (xs : List Bool) : tailProgram.machine.Cfg := ⟨none,none,fun _ => xs⟩

lemma tail_initial (xs : List Bool) : initList tailProgram.machine xs = tailCfg xs := by
  exact (initList_bool tailProgram xs).trans
    (congrArg (fun stk : Unit → List Bool => (⟨some (),none,stk⟩ : tailProgram.machine.Cfg))
      (unit_update (fun _ => []) xs))

lemma tail_final (xs : List Bool) : haltList tailProgram.machine xs = tailEnd xs := by
  exact (haltList_bool tailProgram xs).trans
    (congrArg (fun stk : Unit → List Bool => (⟨none,none,stk⟩ : tailProgram.machine.Cfg))
      (unit_update (fun _ => []) xs))

lemma tail_step_nil : tailProgram.machine.step (tailCfg []) = some (tailEnd []) := by
  simp [FinTM2.step,tailCfg,tailEnd,tailProgram,TM2.step,TM2.stepAux]
  rfl

lemma tail_step_false (xs : List Bool) :
    tailProgram.machine.step (tailCfg (false::xs)) = some (tailEnd xs) := by
  simp [FinTM2.step,tailCfg,tailEnd,tailProgram,TM2.step,TM2.stepAux,unit_update]
  rfl

lemma tail_step_true (xs : List Bool) :
    tailProgram.machine.step (tailCfg (true::xs)) = some (tailCfg xs.tail) := by
  simp [FinTM2.step,tailCfg,tailProgram,TM2.step,TM2.stepAux,unit_update]
  rfl

noncomputable def tail_outputs (xs : List Bool) :
    EvalsToInTime tailProgram.machine.step (tailCfg xs) (some (tailEnd (discardPrefix xs)))
      (xs.length+1) := by
  induction xs using List.twoStepInduction with
  | nil => exact one_step tail_step_nil
  | singleton b =>
    cases b with
    | false => exact time_mono (one_step (tail_step_false [])) (by decide)
    | true => exact step_then (tail_step_true []) (one_step tail_step_nil)
  | cons_cons b c xs ih _ihc =>
    cases b with
    | false => exact time_mono (one_step (tail_step_false (c::xs))) (by simp)
    | true =>
      have hh := step_then (tail_step_true (c::xs)) ih
      exact time_mono hh (by simp)

noncomputable def discardPrefix_computes : PolyComputes discardPrefix where
  program := tailProgram
  time := Polynomial.X+1
  outputs xs := by
    simpa only [TM2OutputsInTime,Option.map_some,tail_initial,tail_final,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using tail_outputs xs

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_ExtractPrefix
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_left _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_one _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_zero _root_.OAI.MetricKMedianRecovery.BitMachine.extractPrefix_pairBits _root_.OAI.MetricKMedianRecovery.BitMachine.frameStacks_inl _root_.OAI.MetricKMedianRecovery.BitMachine.frameStacks_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

abbrev headProgram : Program where
  K := Bool
  input := false
  output := true
  Label := Bool
  main := false
  State := Option Bool
  initial := none
  code l := if l then
    .pop false (fun _ b => b)
      (.branch Option.isSome
        (.load (fun _ => none) (.goto (fun _ => true)))
        (.load (fun _ => none) .halt))
    else
    .pop false (fun _ b => b)
      (.branch (fun s => decide (s = some true))
        (.pop false (fun _ b => b)
          (.branch Option.isSome
            (.push true (fun b => b.getD false) (.load (fun _ => none) (.goto (fun _ => false))))
            (.load (fun _ => none) .halt)))
        (.load (fun _ => none) (.goto (fun _ => true))))

def headCfg (l : Bool) (xs ys : List Bool) : headProgram.machine.Cfg :=
  ⟨some l,none,twoStacks xs ys⟩
def headEnd (ys : List Bool) : headProgram.machine.Cfg :=
  ⟨none,none,twoStacks [] ys⟩

lemma head_initial (xs : List Bool) : initList headProgram.machine xs = headCfg false xs [] := by
  exact (initList_bool headProgram xs).trans
    (congrArg (fun stk : Stacks Bool => (⟨some false,none,stk⟩ : headProgram.machine.Cfg))
      (twoStacks_pure_false xs))

lemma head_final (xs : List Bool) : haltList headProgram.machine xs = headEnd xs := by
  exact (haltList_bool headProgram xs).trans
    (congrArg (fun stk : Stacks Bool => (⟨none,none,stk⟩ : headProgram.machine.Cfg))
      (twoStacks_pure_true xs))

lemma head_clear_nil (ys : List Bool) :
    headProgram.machine.step (headCfg true [] ys) = some (headEnd ys) := by
  simp [FinTM2.step,headCfg,headEnd,headProgram,TM2.step,TM2.stepAux,twoStacks_update_false]
  rfl

lemma head_clear_cons (b : Bool) (xs ys : List Bool) :
    headProgram.machine.step (headCfg true (b::xs) ys) = some (headCfg true xs ys) := by
  simp [FinTM2.step,headCfg,headProgram,TM2.step,TM2.stepAux,twoStacks_update_false]
  rfl

noncomputable def head_clear_outputs (xs ys : List Bool) :
    EvalsToInTime headProgram.machine.step (headCfg true xs ys) (some (headEnd ys)) (xs.length+1) := by
  induction xs with
  | nil => exact one_step (head_clear_nil ys)
  | cons b xs ih => exact step_then (head_clear_cons b xs ys) ih

lemma head_step_nil (ys : List Bool) :
    headProgram.machine.step (headCfg false [] ys) = some (headCfg true [] ys) := by
  simp [FinTM2.step,headCfg,headProgram,TM2.step,TM2.stepAux,twoStacks_update_false]
  rfl

lemma head_step_one (ys : List Bool) :
    headProgram.machine.step (headCfg false [true] ys) = some (headEnd ys) := by
  simp [FinTM2.step,headCfg,headEnd,headProgram,TM2.step,TM2.stepAux,twoStacks_update_false]
  rfl

lemma head_step_false (xs ys : List Bool) :
    headProgram.machine.step (headCfg false (false::xs) ys) = some (headCfg true xs ys) := by
  simp [FinTM2.step,headCfg,headProgram,TM2.step,TM2.stepAux,twoStacks_update_false]
  rfl

lemma head_step_true (b : Bool) (xs ys : List Bool) :
    headProgram.machine.step (headCfg false (true::b::xs) ys) = some (headCfg false xs (b::ys)) := by
  simp [FinTM2.step,headCfg,headProgram,TM2.step,TM2.stepAux,twoStacks_update_false,twoStacks_update_true]
  rfl

noncomputable def head_outputs (xs ys : List Bool) :
    EvalsToInTime headProgram.machine.step (headCfg false xs ys)
      (some (headEnd ((extractPrefix xs).reverse++ys))) (xs.length+2) := by
  induction xs using List.twoStepInduction generalizing ys with
  | nil => exact step_then (head_step_nil ys) (one_step (head_clear_nil ys))
  | singleton b =>
    cases b with
    | false => exact time_mono (step_then (head_step_false [] ys) (head_clear_outputs [] ys)) (by decide)
    | true => exact time_mono (one_step (head_step_one ys)) (by decide)
  | cons_cons b c xs ih _ =>
    cases b with
    | false =>
      exact time_mono (step_then (head_step_false (c::xs) ys) (head_clear_outputs (c::xs) ys)) (by simp)
    | true =>
      have hh := step_then (head_step_true c xs ys) (ih (c::ys))
      simp only [extractPrefix,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp)

noncomputable def extractReverse_computes : PolyComputes (fun xs => (extractPrefix xs).reverse) where
  program := headProgram
  time := Polynomial.X+2
  outputs xs := by
    simpa only [TM2OutputsInTime,Option.map_some,head_initial,head_final,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat,List.append_nil] using head_outputs xs []

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Store2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace WordOperations

abbrev tailProgram : Program where
  K := Unit
  input := ()
  output := ()
  Label := Unit
  main := ()
  State := Unit
  initial := ()
  code _ := .pop () (fun _ _=>()) .halt

end WordOperations

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ProcessOutputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic
namespace Signed

def pack (s : Bool) (x : List Bool) : List Bool :=
  if value x=0 then [false] else s::normalize x

end Signed
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MulComputes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryRational

def divisor (x : List Bool) : List Bool :=
  (Nat.gcd (Signed.mag (numerator x)) (value (denominator x))).bits

def reduceNonzero (x : List Bool) : List Bool :=
  pairBits (Signed.pack (Signed.sign (numerator x))
    (Signed.mag (numerator x)/value (divisor x)).bits,
    (value (denominator x)/value (divisor x)).bits)

def reduce (x : List Bool) : List Bool :=
  if value (denominator x)=0 then encode 0 else reduceNonzero x

end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LeftNum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryRational

def leftNum (x : List Bool) : List Bool := numerator (extractPrefix x)
def rightNum (x : List Bool) : List Bool := numerator (discardPrefix x)
def leftDen (x : List Bool) : List Bool := denominator (extractPrefix x)
def rightDen (x : List Bool) : List Bool := denominator (discardPrefix x)

def rawMul (x : List Bool) : List Bool :=
  pairBits (Signed.encode (Signed.decode (leftNum x)*Signed.decode (rightNum x)),
    (value (leftDen x)*value (rightDen x)).bits)
def rawAdd (x : List Bool) : List Bool :=
  pairBits (Signed.encode (Signed.decode (leftNum x)*(value (rightDen x):ℤ)+
    Signed.decode (rightNum x)*(value (leftDen x):ℤ)),
    (value (leftDen x)*value (rightDen x)).bits)

def addWords : List Bool → List Bool := reduce ∘ rawAdd
def mulWords : List Bool → List Bool := reduce ∘ rawMul

def rawInv (x : List Bool) : List Bool :=
  pairBits (Signed.pack (Signed.sign (numerator x)) (value (denominator x)).bits,
    (Signed.mag (numerator x)).bits)

end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace UnaryTake

lemma projection_bounds (x : List Bool) :
    (counter x).length ≤ x.length ∧ (data x).length ≤ x.length ∧ (output x).length ≤ x.length := by
  have h0 : x.tail.length ≤ x.length := by simp only [List.length_tail]; omega
  have h1 := ProductBits.projections_length x.tail
  have h2 := ProductBits.projections_length (discardPrefix x.tail)
  dsimp only [counter,data,output]; omega

end UnaryTake
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Op
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations
namespace WordList
namespace Zip

def op (x : List Bool) : List Bool :=
  let a := discardPrefix (discardPrefix x)
  let ys := extractPrefix a
  let os := discardPrefix a
  if ys=[] then a else pairBits (WordList.tail ys,cons (pairBits (extractPrefix (discardPrefix x),head ys)) os)

noncomputable def run (x : List Bool) : List Bool := reverse (discardPrefix
  (Fold.run op (4*Polynomial.X+4) (Fold.pack (extractPrefix x) [] (pairBits (discardPrefix x,[])))))
end Zip
end WordList
end
open WordOperations BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyComputes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace UnaryResources

def triple (x : List Bool) : List Bool := (3*value x).bits
end UnaryResources
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RationalArray
noncomputable def addOp : List Bool → List Bool := BinaryRational.addWords ∘ discardPrefix
noncomputable def sumInput (x : List Bool) : List Bool :=
  WordList.Fold.pack x [] (BinaryRational.encode 0)
noncomputable def sumWords : List Bool → List Bool :=
  (WordList.Fold.run addOp (20*(Polynomial.X+1)^2)) ∘ sumInput

noncomputable def mulOp : List Bool → List Bool := BinaryRational.mulWords ∘ discardPrefix
noncomputable def dotWords : List Bool → List Bool :=
  sumWords ∘ ((WordList.mapWith mulOp) ∘ (fun x=>pairBits ([],x)))
noncomputable def dotListsWords : List Bool → List Bool := dotWords ∘ WordList.Zip.run
end RationalArray
attribute [irreducible] RationalArray.sumWords RationalArray.dotWords RationalArray.dotListsWords
namespace RationalMatrix
open WordList

def swapWords (x : List Bool) : List Bool := pairBits (discardPrefix x,extractPrefix x)
def columnOp : List Bool → List Bool := (WordList.mapWith Lookup.run) ∘ swapWords

noncomputable def matrixIndices (x : List Bool) : List Bool := pairBits (x,Indices.run x)
noncomputable def transposeWords : List Bool → List Bool := (mapWith columnOp) ∘ matrixIndices

noncomputable def rightRowOp : List Bool → List Bool := (mapWith RationalArray.dotListsWords) ∘ swapWords
noncomputable def mulInput (x : List Bool) : List Bool :=
  pairBits (transposeWords (discardPrefix x),extractPrefix x)
noncomputable def mulWords : List Bool → List Bool := (mapWith rightRowOp) ∘ mulInput
end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_GetRow2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RationalMatrix
open WordList

def getRow : List Bool → List Bool := Lookup.run ∘ swapWords

def entryInput (x : List Bool) : List Bool := pairBits (discardPrefix x,getRow (extractPrefix x))
def getEntry : List Bool → List Bool := Lookup.run ∘ entryInput

def diagInput (x : List Bool) : List Bool := pairBits (x,discardPrefix x)
def diagAt : List Bool → List Bool := getEntry ∘ diagInput

def contextMatrix (x : List Bool) : List Bool := extractPrefix (extractPrefix x)
def contextIndex (x : List Bool) : List Bool := discardPrefix (extractPrefix x)
def tailDiagInput (x : List Bool) : List Bool := pairBits (contextMatrix x,discardPrefix x)
def tailDiagValue : List Bool → List Bool := diagAt ∘ tailDiagInput

def tailDiagOp (x : List Bool) : List Bool :=
  if value (discardPrefix x)≤value (contextIndex x) then BinaryRational.encode 0 else tailDiagValue x

noncomputable def tailDiagMapInput (x : List Bool) : List Bool :=
  pairBits (x,Indices.run (extractPrefix x))
noncomputable def tailDiagMap : List Bool → List Bool := (mapWith tailDiagOp) ∘ tailDiagMapInput
noncomputable def tailDiag : List Bool → List Bool := RationalArray.sumWords ∘ tailDiagMap

noncomputable def negDiag : List Bool → List Bool :=
  BinaryRational.negWords ∘ tailDiag ∘ extractPrefix
noncomputable def muEntry (x : List Bool) : List Bool :=
  if value (discardPrefix x)≤value (contextIndex x) then
    if value (contextIndex x)≤value (discardPrefix x) then negDiag x else BinaryRational.encode 0
  else getEntry x

noncomputable def muRow : List Bool → List Bool := (mapWith muEntry) ∘ tailDiagMapInput
noncomputable def muWords : List Bool → List Bool := (mapWith muRow) ∘ matrixIndices
noncomputable def stepInput (x : List Bool) : List Bool := pairBits (muWords (discardPrefix x),extractPrefix x)
noncomputable def stepWords (x : List Bool) : List Bool := mulWords (stepInput x)

end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NumAbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
open WordOperations BinaryArithmetic
open scoped Matrix
namespace WordList
noncomputable def pointwise (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  mapWith (f ∘ discardPrefix) (pairBits ([],Zip.run x))
end WordList
namespace BinaryRational

def subInput (x : List Bool) : List Bool := pairBits (extractPrefix x,negWords (discardPrefix x))
def subWords : List Bool → List Bool := addWords ∘ subInput
end BinaryRational
namespace RationalMatrix
open WordList
noncomputable def vectorSub : List Bool → List Bool := pointwise BinaryRational.subWords
noncomputable def vectorScale : List Bool → List Bool := mapWith BinaryRational.mulWords
noncomputable def matrixSub : List Bool → List Bool := pointwise vectorSub
noncomputable def matrixScale : List Bool → List Bool := mapWith vectorScale
noncomputable def outerRow : List Bool → List Bool := vectorScale ∘ swapWords
noncomputable def outer : List Bool → List Bool := (mapWith outerRow) ∘ swapWords
noncomputable def dotRow : List Bool → List Bool := RationalArray.dotListsWords ∘ swapWords
noncomputable def mulVec : List Bool → List Bool := (mapWith dotRow) ∘ swapWords
noncomputable def quadInput (x : List Bool) : List Bool := pairBits (discardPrefix x,mulVec x)
noncomputable def quad : List Bool → List Bool := RationalArray.dotListsWords ∘ quadInput
end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
open scoped Matrix
namespace BinaryEllipsoidCut
open RationalMatrix

def dim : List Bool → List Bool := extractPrefix
def rest : List Bool → List Bool := discardPrefix
def shape : List Bool → List Bool := extractPrefix ∘ rest
def rest₂ : List Bool → List Bool := discardPrefix ∘ rest
def direction : List Bool → List Bool := extractPrefix ∘ rest₂
def rest₃ : List Bool → List Bool := discardPrefix ∘ rest₂
def center : List Bool → List Bool := extractPrefix ∘ rest₃
def precision : List Bool → List Bool := discardPrefix ∘ rest₃

def haInput (x : List Bool) : List Bool := pairBits (shape x,direction x)
noncomputable def haWords : List Bool → List Bool := mulVec ∘ haInput
noncomputable def quadWords : List Bool → List Bool := quad ∘ haInput

def dimension (x : List Bool) : ℚ := value (dim x)
noncomputable def qvalue (x : List Bool) : ℚ := BinaryRational.decode (quadWords x)

def coefA (x : List Bool) : List Bool := BinaryRational.encode (dimension x^2/(dimension x^2-1))
noncomputable def coefB (x : List Bool) : List Bool := BinaryRational.encode (2/((dimension x+1)*qvalue x))
def coefInflate (x : List Bool) : List Bool := BinaryRational.encode (1/(1-1/(8*dimension x^2)))

def rootPrecision (x : List Bool) : ℕ := 32*value (dim x)
noncomputable def coefCenter (x : List Bool) : List Bool :=
  BinaryRational.encode (1/((dimension x+1)*Ellipsoid.rationalRootUpper (rootPrecision x) (qvalue x)))

noncomputable def scaledHaInput (x : List Bool) : List Bool := pairBits (coefCenter x,haWords x)
noncomputable def scaledHa : List Bool → List Bool := vectorScale ∘ scaledHaInput
noncomputable def centerInput (x : List Bool) : List Bool := pairBits (center x,scaledHa x)
noncomputable def centerWords : List Bool → List Bool := vectorSub ∘ centerInput

noncomputable def outerInput (x : List Bool) : List Bool := pairBits (haWords x,haWords x)
noncomputable def outerWords : List Bool → List Bool := outer ∘ outerInput
noncomputable def scaledOuterInput (x : List Bool) : List Bool := pairBits (coefB x,outerWords x)
noncomputable def scaledOuter : List Bool → List Bool := matrixScale ∘ scaledOuterInput
noncomputable def differenceInput (x : List Bool) : List Bool := pairBits (shape x,scaledOuter x)
noncomputable def difference : List Bool → List Bool := matrixSub ∘ differenceInput
noncomputable def cutInput (x : List Bool) : List Bool := pairBits (coefA x,difference x)
noncomputable def cutWords : List Bool → List Bool := matrixScale ∘ cutInput
noncomputable def inflateInput (x : List Bool) : List Bool := pairBits (coefInflate x,cutWords x)
noncomputable def inflateWords : List Bool → List Bool := matrixScale ∘ inflateInput
end BinaryEllipsoidCut
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
open scoped Matrix
namespace BinaryEllipsoidGrid
open RationalMatrix WordList

def dim : List Bool → List Bool := extractPrefix
def rest : List Bool → List Bool := discardPrefix
def precision : List Bool → List Bool := extractPrefix ∘ rest
def shape : List Bool → List Bool := discardPrefix ∘ rest

def ctx : List Bool → List Bool := extractPrefix ∘ extractPrefix
def row : List Bool → List Bool := discardPrefix ∘ extractPrefix
def col : List Bool → List Bool := discardPrefix

def entryInput (x : List Bool) : List Bool := pairBits (pairBits (shape (ctx x),row x),col x)
def entry : List Bool → List Bool := getEntry ∘ entryInput

def dimension (x : List Bool) : ℚ := value (dim (ctx x))
def scale (x : List Bool) : ℚ := value (precision (ctx x))
noncomputable def qvalue (x : List Bool) : ℚ := BinaryRational.decode (entry x)
noncomputable def floorValue (x : List Bool) : ℚ := (⌊scale x*qvalue x⌋:ℤ)/scale x
def diagonal (x : List Bool) : ℚ := dimension x/scale x
noncomputable def entryWords (x : List Bool) : List Bool :=
  if value (row x)≤value (col x) then
    if value (col x)≤value (row x) then BinaryRational.encode (floorValue x+diagonal x)
    else BinaryRational.encode (floorValue x)
  else BinaryRational.encode (floorValue x)

noncomputable def rowInput (x : List Bool) : List Bool := pairBits (x,Indices.run (shape (extractPrefix x)))
noncomputable def rowWords : List Bool → List Bool := (mapWith entryWords) ∘ rowInput

noncomputable def runInput (x : List Bool) : List Bool := pairBits (x,Indices.run (shape x))
noncomputable def run : List Bool → List Bool := (mapWith rowWords) ∘ runInput
end BinaryEllipsoidGrid
namespace BinaryEllipsoidCut
noncomputable def gridInput (x : List Bool) : List Bool := pairBits (dim x,pairBits (precision x,inflateWords x))
noncomputable def shapeWords : List Bool → List Bool := BinaryEllipsoidGrid.run ∘ gridInput
end BinaryEllipsoidCut
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_OptionEncode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations
namespace WordList.Find

def operation (p : List Bool → Bool) (x : List Bool) : List Bool :=
  if accum x=[] then if p (pairBits (context x,item x)) then true::item x else [] else accum x

noncomputable def run (p : List Bool → Bool) : List Bool → List Bool :=
  Fold.run (operation p) (3*Polynomial.X+3) ∘
    (fun x=>Fold.pack (discardPrefix x) (extractPrefix x) [])
end WordList.Find
end
open WordOperations BinaryArithmetic
namespace BinaryRow
open RationalMatrix

def bound : List Bool → List Bool := discardPrefix ∘ discardPrefix
def dotInput (x : List Bool) : List Bool := pairBits (coeff x,extractPrefix x)
noncomputable def dot : List Bool → List Bool := RationalArray.dotListsWords ∘ dotInput
noncomputable def good (x : List Bool) : Bool := decide (BinaryRational.decode (dot x)≤BinaryRational.decode (bound x))
noncomputable def bad (x : List Bool) : Bool := !good x
noncomputable def run : List Bool → List Bool := WordList.Find.run bad
end BinaryRow
namespace BinaryEllipsoidAdvance
open Ellipsoid RationalMatrix
open scoped Matrix

def dim : List Bool → List Bool := extractPrefix
def rest : List Bool → List Bool := discardPrefix
def precision : List Bool → List Bool := extractPrefix ∘ rest
def rest₂ : List Bool → List Bool := discardPrefix ∘ rest
def rows : List Bool → List Bool := extractPrefix ∘ rest₂
def stored : List Bool → List Bool := discardPrefix ∘ rest₂
def shape : List Bool → List Bool := extractPrefix ∘ stored
def center : List Bool → List Bool := discardPrefix ∘ stored
noncomputable def found (x : List Bool) : List Bool := BinaryRow.run (pairBits (center x,rows x))
noncomputable def direction (x : List Bool) : List Bool := extractPrefix (found x).tail

noncomputable def normWords (x : List Bool) : List Bool :=
  RationalArray.dotListsWords (pairBits (direction x,direction x))
noncomputable def zeroDirection (x : List Bool) : Bool := decide (BinaryRational.decode (normWords x)≤0)

noncomputable def cutInput (x : List Bool) : List Bool :=
  pairBits (dim x,pairBits (shape x,pairBits (direction x,pairBits (center x,precision x))))
noncomputable def updated (x : List Bool) : List Bool :=
  pairBits (BinaryEllipsoidCut.shapeWords (cutInput x),BinaryEllipsoidCut.centerWords (cutInput x))
noncomputable def nextState (x : List Bool) : List Bool :=
  if found x=[] then stored x else if zeroDirection x then stored x else updated x
noncomputable def run (x : List Bool) : List Bool :=
  pairBits (dim x,pairBits (precision x,pairBits (rows x,nextState x)))
end BinaryEllipsoidAdvance
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopInput2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RationalMatrix
open WordList

def loopInput (x : List Bool) : List Bool := pairBits (extractPrefix x,discardPrefix (discardPrefix x))
noncomputable def loopOp (x : List Bool) : List Bool := stepWords (loopInput x)

noncomputable def iterationInput (x : List Bool) : List Bool := Fold.pack (WordList.tail x) x x
noncomputable def iterateWords : List Bool → List Bool :=
  (Fold.run loopOp (200*(Polynomial.X+1)^6)) ∘ iterationInput

noncomputable def rawDet : List Bool → List Bool := WordList.head ∘ WordList.head ∘ iterateWords

noncomputable def signOp : List Bool → List Bool :=
  BinaryRational.negWords ∘ discardPrefix ∘ discardPrefix

noncomputable def signRun : List Bool → List Bool := Fold.run signOp (4*Polynomial.X+4)
noncomputable def determinantInput (x : List Bool) : List Bool := Fold.pack (WordList.tail x) [] (rawDet x)
noncomputable def signedDet : List Bool → List Bool := signRun ∘ determinantInput
noncomputable def determinantWords (x : List Bool) : List Bool :=
  if x=[] then BinaryRational.encode 1 else signedDet x
end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic Ellipsoid
namespace BinaryEllipsoidInitial
open RationalMatrix WordList

def ctx : List Bool → List Bool := extractPrefix ∘ extractPrefix
def row : List Bool → List Bool := discardPrefix ∘ extractPrefix
def col : List Bool → List Bool := discardPrefix

def entryWords (x : List Bool) : List Bool :=
  if value (row x)≤value (col x) then
    if value (col x)≤value (row x) then discardPrefix (ctx x) else BinaryRational.encode 0
  else BinaryRational.encode 0

noncomputable def rowInput (x : List Bool) : List Bool :=
  pairBits (x,indices (extractPrefix (extractPrefix x)))
noncomputable def rowWords : List Bool → List Bool := mapWith entryWords ∘ rowInput

noncomputable def runInput (x : List Bool) : List Bool := pairBits (x,indices (extractPrefix x))
noncomputable def run : List Bool → List Bool := mapWith rowWords ∘ runInput

def zeroVector (x : List Bool) : List Bool := repeatWords (pairBits (x,BinaryRational.encode 0))
end BinaryEllipsoidInitial
end
open WordOperations BinaryArithmetic Ellipsoid
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace NaturalArray
open WordList

noncomputable def exponentiate (x : List Bool) : List Bool := productWords (repeatWords x)
noncomputable def unaryLog (x : List Bool) : List Bool :=
  if value x=0 then [true] else RepeatedAppend.copies (BinaryArithmetic.normalize x).length [true]
end NaturalArray
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic Ellipsoid
open UnaryResources
namespace BinaryWeakSolve
open RationalMatrix

def nword : List Bool → List Bool := extractPrefix
def rest₁ : List Bool → List Bool := discardPrefix
def rest₂ : List Bool → List Bool := discardPrefix ∘ rest₁
def rest₃ : List Bool → List Bool := discardPrefix ∘ rest₂
def pword : List Bool → List Bool := extractPrefix ∘ rest₁
def sword : List Bool → List Bool := extractPrefix ∘ rest₂
def radius : List Bool → List Bool := extractPrefix ∘ rest₃
def rows : List Bool → List Bool := discardPrefix ∘ rest₃

def twice (x : List Bool) : List Bool := nword x++nword x
def blocks (x : List Bool) : List Bool :=
  RepeatedAppend.copies (nword x).length (nword x)++
    RepeatedAppend.copies (twice x).length (pword x++sword x)++[true]
def budgetWord (x : List Bool) : List Bool := RepeatedAppend.copies (twice x).length (blocks x)

def radiusSquare (x : List Bool) : List Bool := BinaryRational.encode ((value (radius x):ℚ)*(value (radius x):ℚ))
noncomputable def shapeWords (x : List Bool) : List Bool :=
  BinaryEllipsoidInitial.run (pairBits (nword x,radiusSquare x))

def centerWords (x : List Bool) : List Bool := BinaryEllipsoidInitial.zeroVector (nword x)
noncomputable def result (x : List Bool) : List Bool :=
  if BinaryEllipsoidAdvance.found x=[] then true::BinaryEllipsoidAdvance.center x else []
end BinaryWeakSolve
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic Ellipsoid
namespace BinaryDecision
open UnaryResources NaturalArray

def bound : List Bool → List Bool := extractPrefix ∘ rest₂
end BinaryDecision
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundOp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic Ellipsoid
namespace BinaryDecision
open WordList RationalMatrix

def boundOp (x : List Bool) : List Bool := pairBits (discardPrefix x,extractPrefix x)
noncomputable def boxShape (s : Bool) (x : List Bool) : List Bool :=
  BinaryEllipsoidInitial.run (pairBits (nword x,BinaryRational.encode (if s then 1 else -1)))
noncomputable def boxWords (s : Bool) (x : List Bool) : List Bool :=
  mapWith boundOp (pairBits (BinaryRational.encode (value (bound x):ℚ),boxShape s x))

def relaxedOp (x : List Bool) : List Bool :=
  pairBits (extractPrefix (discardPrefix x),BinaryRational.encode
    (BinaryRational.decode (discardPrefix (discardPrefix x))+BinaryRational.decode (extractPrefix x)))
end BinaryDecision
end
open WordOperations BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundedDecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

namespace BinaryClearRow
open WordOperations BinaryArithmetic Ellipsoid
open WordList RationalMatrix

def entries (x : List Bool) : List Bool := cons (discardPrefix x) (extractPrefix x)
def denOp : List Bool → List Bool := BinaryRational.denominator ∘ discardPrefix
noncomputable def denominators (x : List Bool) : List Bool := mapWith denOp (pairBits ([],entries x))
noncomputable def denominator : List Bool → List Bool := NaturalArray.productWords ∘ denominators
noncomputable def scalar (x : List Bool) : List Bool := BinaryRational.encode (value (denominator x):ℚ)
noncomputable def coeffWords (x : List Bool) : List Bool := mapWith BinaryRational.mulWords (pairBits (scalar x,extractPrefix x))
noncomputable def boundWords (x : List Bool) : List Bool := BinaryRational.encode
  ((value (denominator x):ℚ)*BinaryRational.decode (discardPrefix x))
noncomputable def run (x : List Bool) : List Bool := pairBits (coeffWords x,boundWords x)
end BinaryClearRow
namespace BinaryRationalDecision
open WordOperations BinaryArithmetic Ellipsoid
open WordList

def second : List Bool → List Bool := extractPrefix ∘ rest₁
noncomputable def clearOp : List Bool → List Bool := BinaryClearRow.run ∘ discardPrefix
noncomputable def clearedRows (x : List Bool) : List Bool := mapWith clearOp (pairBits ([],rows x))
noncomputable def prepared (x : List Bool) : List Bool :=
  pairBits (first x,pairBits (second x,pairBits (bound x,clearedRows x)))
end BinaryRationalDecision

open WordOperations
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FaceSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic Ellipsoid
namespace BinaryFinalFace
open WordList BinaryRationalDecision
noncomputable def shape (s : Bool) (x : List Bool) : List Bool :=
  BinaryEllipsoidInitial.run (pairBits (first x,BinaryRational.encode (if s then 1 else -1)))
noncomputable def box (s : Bool) (x : List Bool) : List Bool :=
  mapWith BinaryDecision.boundOp (pairBits (BinaryRational.encode (value (bound x)),shape s x))
noncomputable def allRows (x : List Bool) : List Bool := rows x++(box true x++box false x)
noncomputable def context (x : List Bool) : List Bool :=
  pairBits (first x,pairBits (Count.run (allRows x),pairBits (bound x,allRows x)))
end BinaryFinalFace
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList.Set

def pack (xs j v : List Bool) : List Bool := pairBits (xs,pairBits (j,v))
def target (x : List Bool) : List Bool := extractPrefix (discardPrefix (extractPrefix x))
def replacement (x : List Bool) : List Bool := discardPrefix (discardPrefix (extractPrefix x))
def oldInput (x : List Bool) : List Bool := pairBits (discardPrefix x,extractPrefix (extractPrefix x))
def oldValue (x : List Bool) : List Bool := Lookup.run (oldInput x)

def op (x : List Bool) : List Bool :=
  if value (discardPrefix x)≤value (target x) then
    if value (target x)≤value (discardPrefix x) then replacement x else oldValue x
  else oldValue x

noncomputable def input (x : List Bool) : List Bool := pairBits (x,Indices.run (extractPrefix x))
noncomputable def run (x : List Bool) : List Bool := mapWith op (input x)
end WordList.Set
open WordOperations BinaryArithmetic
open scoped Matrix
namespace RationalMatrix
open WordList

noncomputable def updateInput (x : List Bool) : List Bool :=
  Set.pack (transposeWords (extractPrefix x)) (extractPrefix (discardPrefix x))
    (discardPrefix (discardPrefix x))

def cramerOpInput (x : List Bool) : List Bool :=
  Set.pack (extractPrefix (extractPrefix x)) (discardPrefix x) (discardPrefix (extractPrefix x))
noncomputable def cramerInput (x : List Bool) : List Bool := pairBits (x,Indices.run (extractPrefix x))
end RationalMatrix
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
open WordOperations BinaryArithmetic Matrix
namespace Rectangular
open WordList RationalMatrix

noncomputable def transpose (x : List Bool) : List Bool :=
  mapWith columnOp (pairBits (discardPrefix x,BinaryEllipsoidInitial.indices (extractPrefix x)))
end Rectangular
end

open WordOperations BinaryArithmetic Ellipsoid Matrix
namespace BinaryExactSolve
open WordList BinaryRationalDecision RationalMatrix
noncomputable def bounds (x : List Bool) : List Bool := mapWith BinaryRow.bound (pairBits ([],x))
end BinaryExactSolve
end MetricKMedianRecovery.BitMachine

end OAI
end


