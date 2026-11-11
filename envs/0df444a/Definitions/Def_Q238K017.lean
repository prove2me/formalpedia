-- Prove2me | Definitions.Def_Q238K017
-- name    : Q238K017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:15:33.246278+00:00
-- url     : https://prove2.me/theorems/77172af0-c6cb-4e1e-ab93-755a31a803ee
-- title:
--   Definitions bundle Q238K017 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 127 declarations of OpenAI's Lean: 65 definitions and 62 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.coefInflate`, `OAI.MetricKMedianRecovery.BitMachine.FiniteFold.cfg`, `OAI.MetricKMedianRecovery.BitMachine.FiniteFold.computes`, `OAI.MetricKMedianRecovery.BitMachine.FiniteFold.done`, `OAI.MetricKMedianRecovery.BitMachine.FiniteFold.finish`, `OAI.MetricKMedianRecovery.BitMachine.FiniteFold.outputs`, `OAI.MetricKMedianRecovery.BitMachine.FiniteFold.program`, `OAI.MetricKMedianRecovery.BitMachine.PolyComputes.append`, `OAI.MetricKMedianRecovery.BitMachine.PolyComputes.cond`, `OAI.MetricKMedianRecovery.BitMachine.PolyComputes.pair`, `OAI.MetricKMedianRecovery.BitMachine.PolyComputes.sameIO`, `OAI.MetricKMedianRecovery.BitMachine.PolyComputes.whileLoop`, `OAI.MetricKMedianRecovery.BitMachine.PolynomialCounter.add`, `OAI.MetricKMedianRecovery.BitMachine.PolynomialCounter.constant`, `OAI.MetricKMedianRecovery.BitMachine.PolynomialCounter.identity`, `OAI.MetricKMedianRecovery.BitMachine.ProductBits.parse_phase`, `OAI.MetricKMedianRecovery.BitMachine.ProductBits.swap_computes`, `OAI.MetricKMedianRecovery.BitMachine.SameIO.baseCfg`, `OAI.MetricKMedianRecovery.BitMachine.SameIO.baseStack`, `OAI.MetricKMedianRecovery.BitMachine.SameIO.firstCfg`, `OAI.MetricKMedianRecovery.BitMachine.SameIO.firstStack`, `OAI.MetricKMedianRecovery.BitMachine.SameIO.outputs`, `OAI.MetricKMedianRecovery.BitMachine.SameIO.program`, `OAI.MetricKMedianRecovery.BitMachine.SameIO.secondCfg`, `OAI.MetricKMedianRecovery.BitMachine.SameIO.secondStack`, `OAI.MetricKMedianRecovery.BitMachine.UnaryTake.pack_computes`, `OAI.MetricKMedianRecovery.BitMachine.While.advance`, `OAI.MetricKMedianRecovery.BitMachine.While.controlCfg`, `OAI.MetricKMedianRecovery.BitMachine.While.outputs`, `OAI.MetricKMedianRecovery.BitMachine.While.program`, `OAI.MetricKMedianRecovery.BitMachine.While.runCfg`, `OAI.MetricKMedianRecovery.BitMachine.WordOperations.appendProgram`, `OAI.MetricKMedianRecovery.BitMachine.WordOperations.append_computes`, `OAI.MetricKMedianRecovery.BitMachine.WordOperations.cfg`, `OAI.MetricKMedianRecovery.BitMachine.WordOperations.done`, `OAI.MetricKMedianRecovery.BitMachine.WordOperations.parse_phase`, `OAI.MetricKMedianRecovery.BitMachine.WordOperations.restore_phase`, `OAI.MetricKMedianRecovery.BitMachine.WordOperations.tailProgram`, `OAI.MetricKMedianRecovery.BitMachine.WordOperations.tail_computes`, `OAI.MetricKMedianRecovery.BitMachine.WordSelection.cfg` and 25 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedianRecovery_Encoding_PushWord`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/PushWord.lean), [`KMedianRecovery_Encoding_RationalLeaves`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/RationalLeaves.lean), [`KMedianRecovery_Machines_Program2`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/Program2.lean), [`KMedianRecovery_Recovery_Computes`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Computes.lean), [`KMedianRecovery_Recovery_Copies`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Copies.lean), [`KMedianRecovery_Recovery_Pack3`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Pack3.lean), [`KMedianRecovery_Recovery_Pack5`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Pack5.lean), [`KMedianRecovery_Recovery_Stack2`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Stack2.lean), [`KMedianRecovery_Recovery_StepThen`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/StepThen.lean), [`KMedianRecovery_Recovery_Store`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Store.lean), [`KMedianRecovery_Recovery_Store2`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Store2.lean), [`KMedianRecovery_Sampling_ExtractPrefix`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/ExtractPrefix.lean).
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K006`, `Q238K007` and `Q238K010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K024`, `Q238K025`, `Q238K026` and `Q238K027`; the statements `OAI.MetricKMedianRecovery.RationalLeaves.prefix_leaf_s238` and `OAI.MetricKMedianRecovery.RationalLeaves.zero_free_replay_s238`; the proofs of `OAI.MetricKMedianRecovery.RationalLeaves.prefix_leaf_s238` and `OAI.MetricKMedianRecovery.RationalLeaves.zero_free_replay_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K006
import Definitions.Def_Q238K007
import Definitions.Def_Q238K010

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_StepThen
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_left _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_one _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_zero
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

abbrev reverseProgram : Program where
  K := Bool
  input := false
  output := true
  Label := Unit
  main := ()
  State := Option Bool
  initial := none
  code _ := .pop false (fun _ b => b)
    (.branch Option.isSome
      (.push true (fun b => b.getD false) (.load (fun _ => none) (.goto (fun _ => ()))))
      (.load (fun _ => none) .halt))

def reverseCfg (xs ys : List Bool) : reverseProgram.machine.Cfg :=
  ⟨some (),none,twoStacks xs ys⟩
def reverseEnd (ys : List Bool) : reverseProgram.machine.Cfg :=
  ⟨none,none,twoStacks [] ys⟩

lemma reverse_initial (xs : List Bool) : initList reverseProgram.machine xs = reverseCfg xs [] := by
  exact (initList_bool reverseProgram xs).trans
    (congrArg (fun stk : Stacks Bool => (⟨some (),none,stk⟩ : reverseProgram.machine.Cfg))
      (twoStacks_pure_false xs))

lemma reverse_final (xs : List Bool) : haltList reverseProgram.machine xs = reverseEnd xs := by
  exact (haltList_bool reverseProgram xs).trans
    (congrArg (fun stk : Stacks Bool => (⟨none,none,stk⟩ : reverseProgram.machine.Cfg))
      (twoStacks_pure_true xs))

lemma reverse_step_nil (ys : List Bool) :
    reverseProgram.machine.step (reverseCfg [] ys) = some (reverseEnd ys) := by
  simp [FinTM2.step,reverseCfg,reverseEnd,reverseProgram,TM2.step,TM2.stepAux,twoStacks_update_false]
  rfl

lemma reverse_step_cons (b : Bool) (xs ys : List Bool) :
    reverseProgram.machine.step (reverseCfg (b::xs) ys) = some (reverseCfg xs (b::ys)) := by
  simp [FinTM2.step,reverseCfg,reverseProgram,TM2.step,TM2.stepAux,
    twoStacks_update_false,twoStacks_update_true]
  rfl

noncomputable def reverse_outputs (xs ys : List Bool) :
    EvalsToInTime reverseProgram.machine.step (reverseCfg xs ys) (some (reverseEnd (xs.reverse++ys)))
      (xs.length+1) := by
  induction xs generalizing ys with
  | nil => exact one_step (reverse_step_nil ys)
  | cons b xs ih =>
    have hh := step_then (reverse_step_cons b xs ys) (ih (b::ys))
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hh

noncomputable def reverse_computes : PolyComputes List.reverse where
  program := reverseProgram
  time := Polynomial.X+1
  outputs xs := by
    simpa only [List.append_nil,TM2OutputsInTime,Option.map_some,reverse_initial,reverse_final,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using reverse_outputs xs []

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_PushWord
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_left _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_one _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

namespace FiniteFold
variable {Q : Type} [Fintype Q] (q₀ : Q) (next : Q → Bool → Q) (out : Q → List Bool)

abbrev program : Program where
  K := Unit
  input := ()
  output := ()
  Label := Option Q
  main := none
  State := Q × Option Bool
  initial := (q₀,none)
  code l := match l with
    | none => .pop () (fun q b=>(q.1,b))
      (.branch (fun q=>q.2.isSome)
        (.load (fun q=>(next q.1 (q.2.getD false),none)) (.goto (fun _=>none)))
        (.goto (fun q=>some q.1)))
    | some q => pushWord () (out q) (.load (fun _=>(q₀,none)) .halt)

def cfg (q : Q) (xs : List Bool) : (program q₀ next out).machine.Cfg :=
  ⟨some none,(q,none),fun _=>xs⟩
def finish (q : Q) : (program q₀ next out).machine.Cfg :=
  ⟨some (some q),(q,none),fun _=>[]⟩
def done (xs : List Bool) : (program q₀ next out).machine.Cfg :=
  ⟨none,(q₀,none),fun _=>xs⟩

lemma nil_step (q : Q) : (program q₀ next out).machine.step (cfg q₀ next out q [])=
    some (finish q₀ next out q) := by
  simp [FinTM2.step,program,cfg,finish,TM2.step,TM2.stepAux]
  rfl
lemma cons_step (q : Q) (b : Bool) (xs : List Bool) :
    (program q₀ next out).machine.step (cfg q₀ next out q (b::xs))=
      some (cfg q₀ next out (next q b) xs) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,unit_update]
  rfl
lemma finish_step (q : Q) : (program q₀ next out).machine.step (finish q₀ next out q)=
    some (done q₀ next out (out q)) := by
  simp [FinTM2.step,program,finish,done,TM2.step,pushWord_step,TM2.stepAux,unit_update]
  rfl

noncomputable def outputs (q : Q) (xs : List Bool) :
    EvalsToInTime (program q₀ next out).machine.step (cfg q₀ next out q xs)
      (some (done q₀ next out (out (xs.foldl next q)))) (xs.length+2) := by
  induction xs generalizing q with
  | nil => exact step_then (nil_step q₀ next out q) (one_step (finish_step q₀ next out q))
  | cons b xs ih =>
    simpa only [List.foldl_cons,List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
      step_then (cons_step q₀ next out q b xs) (ih (next q b))

lemma initial (xs : List Bool) : initList (program q₀ next out).machine xs=cfg q₀ next out q₀ xs := by
  rw [initList_bool]
  congr 1
lemma final (xs : List Bool) : haltList (program q₀ next out).machine xs=done q₀ next out xs := by
  rw [haltList_bool]
  congr 1

noncomputable def computes : PolyComputes (fun xs=>out (xs.foldl next q₀)) where
  program := program q₀ next out
  time := Polynomial.X+2
  outputs xs := by
    simpa only [TM2OutputsInTime,Option.map_some,initial,final,Polynomial.eval_add,Polynomial.eval_X,
      Polynomial.eval_ofNat] using outputs q₀ next out q₀ xs

end FiniteFold

noncomputable def isEmpty_computes : PolyComputes (fun xs=>[decide (xs=[])]) := by
  have hh := FiniteFold.computes true (fun _ _=>false) (fun q=>[q])
  simpa [fold_empty] using hh

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [PseudoMetricSpace V]

attribute [local instance] metric

def original : V ↪ Label V := ⟨Sum.inl,Sum.inl_injective⟩

end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_ExtractPrefix
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_left _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_one _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_zero _root_.OAI.MetricKMedianRecovery.BitMachine.frameStacks_inl _root_.OAI.MetricKMedianRecovery.BitMachine.frameStacks_inr
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

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Stack2
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_left _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_one _root_.OAI.MetricKMedianRecovery.BitMachine.MapLeft.stacks_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace SameIO
variable (p : Program)

def baseStack : p.K ↪ Stack p := ⟨Sum.inl,Sum.inl_injective⟩
def firstStack : Bool ↪ Stack p where
  toFun b := cond b (Sum.inr ()) (Sum.inl p.output)
  inj' := by intro a b h; cases a <;> cases b <;> simp_all
def secondStack : Bool ↪ Stack p where
  toFun b := cond b (Sum.inl p.input) (Sum.inr ())
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

noncomputable abbrev program : Program where
  K := Stack p
  input := Sum.inl p.input
  output := Sum.inl p.input
  Label := p.Label ⊕ Bool
  main := Sum.inl p.main
  State := p.State × Option Bool
  initial := (p.initial,none)
  code l := match l with
    | .inl l => renameStmt (baseStack p) Sum.inl (fun s => (s,none)) Prod.fst
        (some (Sum.inr false)) (p.code l)
    | .inr false => renameStmt (firstStack p) (fun _ => Sum.inr false)
        (fun s => (p.initial,s)) Prod.snd (some (Sum.inr true)) (reverseProgram.code ())
    | .inr true => renameStmt (secondStack p) (fun _ => Sum.inr true)
        (fun s => (p.initial,s)) Prod.snd none (reverseProgram.code ())

noncomputable def baseCfg : p.machine.Cfg → (program p).machine.Cfg :=
  renameCfg (baseStack p) Sum.inl (fun s => (s,none)) (some (Sum.inr false))
noncomputable def firstCfg : reverseProgram.machine.Cfg → (program p).machine.Cfg :=
  renameCfg (firstStack p) (fun _ => Sum.inr false) (fun s => (p.initial,s)) (some (Sum.inr true))
noncomputable def secondCfg : reverseProgram.machine.Cfg → (program p).machine.Cfg :=
  renameCfg (secondStack p) (fun _ => Sum.inr true) (fun s => (p.initial,s)) none

lemma base_step (s t : p.machine.Cfg) (h : p.machine.step s = some t) :
    (program p).machine.step (baseCfg p s) = some (baseCfg p t) := by
  rcases s with ⟨l,v,stk⟩
  cases l with
  | none => simp only [FinTM2.step,TM2.step] at h; contradiction
  | some l =>
    simp only [FinTM2.step,TM2.step] at h
    have ht := Option.some.inj h
    subst t
    change some (TM2.stepAux (renameStmt (baseStack p) Sum.inl (fun s => (s,none)) Prod.fst
      (some (Sum.inr false)) (p.code l)) (v,none) (embedStacks (baseStack p) stk)) = _
    rw [stepAux_rename _ _ _ _ (fun _ => rfl)]
    rfl

lemma first_step (s t : reverseProgram.machine.Cfg) (h : reverseProgram.machine.step s = some t) :
    (program p).machine.step (firstCfg p s) = some (firstCfg p t) := by
  rcases s with ⟨l,v,stk⟩
  cases l with
  | none => simp only [FinTM2.step,TM2.step] at h; contradiction
  | some l =>
    cases l
    simp only [FinTM2.step,TM2.step] at h
    have ht := Option.some.inj h
    subst t
    change some (TM2.stepAux (renameStmt (firstStack p) (fun _ => Sum.inr false)
      (fun s => (p.initial,s)) Prod.snd (some (Sum.inr true)) (reverseProgram.code ()))
      (p.initial,v) (embedStacks (firstStack p) stk)) = _
    rw [stepAux_rename _ _ _ _ (fun _ => rfl)]
    rfl

lemma second_step (s t : reverseProgram.machine.Cfg) (h : reverseProgram.machine.step s = some t) :
    (program p).machine.step (secondCfg p s) = some (secondCfg p t) := by
  rcases s with ⟨l,v,stk⟩
  cases l with
  | none => simp only [FinTM2.step,TM2.step] at h; contradiction
  | some l =>
    cases l
    simp only [FinTM2.step,TM2.step] at h
    have ht := Option.some.inj h
    subst t
    change some (TM2.stepAux (renameStmt (secondStack p) (fun _ => Sum.inr true)
      (fun s => (p.initial,s)) Prod.snd none (reverseProgram.code ()))
      (p.initial,v) (embedStacks (secondStack p) stk)) = _
    rw [stepAux_rename _ _ _ _ (fun _ => rfl)]
    rfl

lemma base_initial (bits : List Bool) :
    baseCfg p (initList p.machine bits) = initList (program p).machine bits := by
  rw [initList_bool,initList_bool]
  change (⟨some (Sum.inl p.main),(p.initial,none),
    embedStacks (baseStack p) (Function.update (fun _ => []) p.input bits)⟩ : (program p).machine.Cfg) = _
  rw [embedStacks_pure]
  rfl

lemma first_handoff (bits : List Bool) :
    baseCfg p (haltList p.machine bits) = firstCfg p (initList reverseProgram.machine bits) := by
  rw [haltList_bool,initList_bool]
  change (⟨some (Sum.inr false),(p.initial,none),
    embedStacks (baseStack p) (Function.update (fun _ => []) p.output bits)⟩ : (program p).machine.Cfg) =
    ⟨some (Sum.inr false),(p.initial,none),
    embedStacks (firstStack p) (Function.update (fun _ => []) false bits)⟩
  rw [embedStacks_pure,embedStacks_pure]
  rfl

lemma second_handoff (bits : List Bool) :
    firstCfg p (haltList reverseProgram.machine bits) = secondCfg p (initList reverseProgram.machine bits) := by
  rw [haltList_bool,initList_bool]
  change (⟨some (Sum.inr true),(p.initial,none),
    embedStacks (firstStack p) (Function.update (fun _ => []) true bits)⟩ : (program p).machine.Cfg) =
    ⟨some (Sum.inr true),(p.initial,none),
    embedStacks (secondStack p) (Function.update (fun _ => []) false bits)⟩
  rw [embedStacks_pure,embedStacks_pure]
  rfl

lemma second_final (bits : List Bool) :
    secondCfg p (haltList reverseProgram.machine bits) = haltList (program p).machine bits := by
  rw [haltList_bool,haltList_bool]
  change (⟨none,(p.initial,none),
    embedStacks (secondStack p) (Function.update (fun _ => []) true bits)⟩ : (program p).machine.Cfg) = _
  rw [embedStacks_pure]
  rfl

noncomputable def outputs {x y : List Bool} {m : ℕ}
    (h : TM2OutputsInTime p.machine x (some y) m) :
    TM2OutputsInTime (program p).machine x (some y) (m+2*(y.length+1)) := by
  have h1 := reverse_computes.outputs y
  have h2 := reverse_computes.outputs y.reverse
  have h0' := iterate_transfer p.machine.step (program p).machine.step (baseCfg p) (base_step p)
    h.steps (initList p.machine x) (haltList p.machine y) h.evals_in_steps
  have h1' := iterate_transfer reverseProgram.machine.step (program p).machine.step (firstCfg p) (first_step p)
    h1.steps (initList reverseProgram.machine y) (haltList reverseProgram.machine y.reverse) h1.evals_in_steps
  have h2' := iterate_transfer reverseProgram.machine.step (program p).machine.step (secondCfg p) (second_step p)
    h2.steps (initList reverseProgram.machine y.reverse) (haltList reverseProgram.machine y.reverse.reverse) h2.evals_in_steps
  rw [base_initial,first_handoff] at h0'
  rw [second_handoff] at h1'
  rw [second_final] at h2'
  simp only [List.reverse_reverse] at h2'
  refine ⟨⟨h2.steps+(h1.steps+h.steps),?_⟩,?_⟩
  · change (fun s : Option (program p).machine.Cfg => s.bind (program p).machine.step)^[h2.steps+(h1.steps+h.steps)]
      (some (initList (program p).machine x)) = some (haltList (program p).machine y)
    rw [Function.iterate_add_apply,Function.iterate_add_apply,h0',h1',h2']
  · change h2.steps+(h1.steps+h.steps) ≤ m+2*(y.length+1)
    have hm0 := h.steps_le_m
    have hm1 := h1.steps_le_m
    have hm2 := h2.steps_le_m
    simp only [reverse_computes,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,List.length_reverse] at hm1 hm2
    omega

end SameIO

noncomputable def PolyComputes.sameIO {f : List Bool → List Bool} (h : PolyComputes f) : PolyComputes f where
  program := SameIO.program h.program
  time := h.time+2*(Polynomial.X+h.time*Polynomial.C h.program.maxPush+1)
  outputs x := by
    have hh := SameIO.outputs h.program (h.outputs x)
    refine ⟨hh.toEvalsTo,?_⟩
    apply hh.steps_le_m.trans
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_ofNat,
      Polynomial.eval_one]
    have hl := h.program.output_length (h.outputs x)
    omega

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_Program2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

lemma embedStacks_refl {K : Type} (s : Stacks K) : embedStacks (Function.Embedding.refl K) s = s := by
  funext k
  exact embedStacks_apply (Function.Embedding.refl K) s k

namespace While
variable (p : Program)

noncomputable abbrev program : Program where
  K := p.K
  input := p.input
  output := p.input
  Label := Option p.Label
  main := none
  State := p.State × Option Bool
  initial := (p.initial,none)
  code l := match l with
    | none => .peek p.input (fun _ b => (p.initial,b))
        (.branch (fun s => decide (s.2 = some true))
          (.load (fun _ => (p.initial,none)) (.goto (fun _ => some p.main)))
          (.load (fun _ => (p.initial,none)) .halt))
    | some l => renameStmt (Function.Embedding.refl p.K) some (fun s => (s,none)) Prod.fst
        (some none) (p.code l)

noncomputable def runCfg : p.machine.Cfg → (program p).machine.Cfg :=
  renameCfg (Function.Embedding.refl p.K) some (fun s => (s,none)) (some none)
def controlCfg (x : List Bool) : (program p).machine.Cfg :=
  ⟨some none,(p.initial,none),Function.update (fun _ => []) p.input x⟩

lemma run_step (s t : p.machine.Cfg) (h : p.machine.step s = some t) :
    (program p).machine.step (runCfg p s) = some (runCfg p t) := by
  rcases s with ⟨l,v,stk⟩
  cases l with
  | none => simp only [FinTM2.step,TM2.step] at h; contradiction
  | some l =>
    simp only [FinTM2.step,TM2.step] at h
    have ht := Option.some.inj h
    subst t
    change some (TM2.stepAux (renameStmt (Function.Embedding.refl p.K) some (fun s => (s,none)) Prod.fst
      (some none) (p.code l)) (v,none) (embedStacks (Function.Embedding.refl p.K) stk)) = _
    rw [stepAux_rename _ _ _ _ (fun _ => rfl)]
    rfl

lemma initial (x : List Bool) : initList (program p).machine x = controlCfg p x := by
  rw [initList_bool]
  rfl

lemma start (x : List Bool) (h : x.head? = some true) :
    (program p).machine.step (controlCfg p x) = some (runCfg p (initList p.machine x)) := by
  rw [initList_bool]
  simp only [FinTM2.step,controlCfg,program,TM2.step,TM2.stepAux,Function.update_self,h,
    decide_true,Bool.cond_true,runCfg,renameCfg,Option.elim_some,embedStacks_refl]
  rfl

lemma stop (x : List Bool) (h : x.head? ≠ some true) :
    (program p).machine.step (controlCfg p x) = some (haltList (program p).machine x) := by
  rw [haltList_bool]
  simp only [FinTM2.step,controlCfg,program,TM2.step,TM2.stepAux,Function.update_self,h,
    decide_false,Bool.cond_false]
  rfl

lemma handoff (he : p.output = p.input) (x : List Bool) :
    runCfg p (haltList p.machine x) = controlCfg p x := by
  rw [haltList_bool]
  change (⟨some none,(p.initial,none),
    embedStacks (Function.Embedding.refl p.K) (Function.update (fun _ => []) p.output x)⟩ : (program p).machine.Cfg) = _
  rw [embedStacks_refl,he]
  rfl

noncomputable def advance {x y : List Bool} {m : ℕ} (he : p.output = p.input)
    (hstart : x.head? = some true) (h : TM2OutputsInTime p.machine x (some y) m) :
    EvalsToInTime (program p).machine.step (controlCfg p x) (some (controlCfg p y)) (m+1) := by
  have hh := iterate_transfer p.machine.step (program p).machine.step (runCfg p) (run_step p)
    h.steps (initList p.machine x) (haltList p.machine y) h.evals_in_steps
  rw [handoff p he] at hh
  exact step_then (start p x hstart) ⟨⟨h.steps,hh⟩,h.steps_le_m⟩

noncomputable def outputs (he : p.output = p.input) (f : List Bool → List Bool) (P : Polynomial ℕ)
    (hf : ∀ x, TM2OutputsInTime p.machine x (some (f x)) (P.eval x.length))
    (n B : ℕ) (x : List Bool)
    (hB : ∀ j ≤ n, ((next f)^[j] x).length ≤ B)
    (hstop : ((next f)^[n] x).head? ≠ some true) :
    EvalsToInTime (program p).machine.step (controlCfg p x)
      (some (haltList (program p).machine ((next f)^[n] x))) (n*(P.eval B+1)+1) := by
  induction n generalizing x with
  | zero => simpa only [Function.iterate_zero_apply,Nat.zero_mul,Nat.zero_add] using one_step (stop p x hstop)
  | succ n ih =>
    by_cases hx : x.head? = some true
    · have hnext : next f x = f x := ite_eq_left hx
      have hBn : ∀ j ≤ n, ((next f)^[j] (f x)).length ≤ B := by
        intro j hj
        have hh := hB (j+1) (Nat.add_le_add_right hj 1)
        simpa only [Function.iterate_succ_apply,hnext] using hh
      have hstopn : ((next f)^[n] (f x)).head? ≠ some true := by
        simpa only [Function.iterate_succ_apply,hnext] using hstop
      have hi := ih (f x) hBn hstopn
      have ha := advance p he hx (hf x)
      have hh := eval_trans ha hi
      have hlen : x.length ≤ B := hB 0 (Nat.zero_le _)
      have ht : P.eval x.length ≤ P.eval B := polynomial_monotone P hlen
      simp only [Function.iterate_succ_apply,hnext]
      exact time_mono hh (by simp only [Nat.succ_mul]; omega)
    · rw [next_fixed f x hx]
      exact time_mono (one_step (stop p x hx)) (by omega)

end While

noncomputable def PolyComputes.whileLoop {f : List Bool → List Bool} (hf : PolyComputes f)
    (fuel : List Bool → ℕ) (Q R : Polynomial ℕ)
    (hq : ∀ x, fuel x ≤ Q.eval x.length)
    (hr : ∀ x j, j ≤ fuel x → ((While.next f)^[j] x).length ≤ R.eval x.length)
    (hs : ∀ x, ((While.next f)^[fuel x] x).head? ≠ some true) :
    PolyComputes (fun x => (While.next f)^[fuel x] x) where
  program := While.program hf.sameIO.program
  time := Q*(hf.sameIO.time.comp R+1)+1
  outputs x := by
    have hh := While.outputs hf.sameIO.program rfl f hf.sameIO.time hf.sameIO.outputs (fuel x)
      (R.eval x.length) x (hr x) (hs x)
    change TM2OutputsInTime (While.program hf.sameIO.program).machine x
      (some ((While.next f)^[fuel x] x)) _
    unfold TM2OutputsInTime
    rw [While.initial]
    refine ⟨hh.toEvalsTo,?_⟩
    apply hh.steps_le_m.trans
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_one]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (hq x)) 1

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Store
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.discardPrefix_pairBits _root_.OAI.MetricKMedianRecovery.BitMachine.extractPrefix_pairBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace ProductBits

noncomputable def parse_phase (a b : List Bool) :
    EvalsToInTime (program false).machine.step (cfg false 0 a b [])
      (some (cfg false 1 (discardPrefix a) ((extractPrefix a).reverse++b) [])) (a.length+1) := by
  induction a using List.twoStepInduction generalizing b with
  | nil => exact one_step (parse_nil b)
  | singleton x =>
    cases x with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_cons,List.length_nil] using
        time_mono (one_step (parse_false [] b)) (by decide : 1≤2)
    | true => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_cons,List.length_nil] using
        time_mono (one_step (parse_one b)) (by decide : 1≤2)
  | cons_cons x y a ih _ =>
    cases x with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append] using
        time_mono (one_step (parse_false (y::a) b)) (by simp : 1≤(false::y::a).length+1)
    | true =>
      have hh := step_then (parse_true y a b) (ih (y::b))
      simp only [extractPrefix,discardPrefix,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp)

noncomputable def swap_computes : PolyComputes (fun xs => pairBits (discardPrefix xs,extractPrefix xs)) where
  program := program false
  time := 4*Polynomial.X+4
  outputs xs := by
    let a := extractPrefix xs
    let b := discardPrefix xs
    have h1 := parse_phase xs []
    have h2 := reverse_phase false b a.reverse []
    have h3 := restore_phase false [] a.reverse b.reverse
    have h4 := encode_phase false (false::a) b.reverse
    simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h1 h2 h3 h4
    have hh := eval_trans h1 (eval_trans h2 (eval_trans h3 h4))
    simp only [TM2OutputsInTime,Option.map_some,initial,final,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_X,pairBits,List.append_assoc,List.cons_append,List.nil_append]
    apply time_mono hh
    have hp := projections_length xs
    change a.length≤xs.length ∧ b.length≤xs.length at hp
    omega

end ProductBits

noncomputable def PolyComputes.pair {f g : List Bool → List Bool}
    (hf : PolyComputes f) (hg : PolyComputes g) : PolyComputes (fun xs=>pairBits (f xs,g xs)) := by
  have h := (((ProductBits.duplicate_computes.comp hf.mapLeft).comp ProductBits.swap_computes).comp
    hg.mapLeft).comp ProductBits.swap_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair] using h

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Store2
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.discardPrefix_pairBits _root_.OAI.MetricKMedianRecovery.BitMachine.extractPrefix_pairBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace WordOperations

lemma upd1 (xs ys zs : List Bool) : Function.update (store xs ys) 1 zs=store xs zs := by
  funext i; fin_cases i <;> simp [store]

abbrev appendProgram : Program where
  K := Fin 2
  input := 0
  output := 0
  Label := Bool
  main := false
  State := Option Bool
  initial := none
  code l := if l then
    .pop 1 (fun _ b=>b)
      (.branch Option.isSome
        (.push 0 (fun s=>s.getD false) (.load (fun _=>none) (.goto (fun _=>true))))
        (.load (fun _=>none) .halt))
    else
      .pop 0 (fun _ b=>b)
        (.branch (fun s=>decide (s=some true))
          (.pop 0 (fun _ b=>b)
            (.branch Option.isSome
              (.push 1 (fun s=>s.getD false) (.load (fun _=>none) (.goto (fun _=>false))))
              (.load (fun _=>none) (.goto (fun _=>true)))))
          (.load (fun _=>none) (.goto (fun _=>true))))

def cfg (l : Bool) (xs ys : List Bool) : appendProgram.machine.Cfg := ⟨some l,none,store xs ys⟩
def done (xs : List Bool) : appendProgram.machine.Cfg := ⟨none,none,store xs []⟩

lemma parse_nil (ys : List Bool) : appendProgram.machine.step (cfg false [] ys)=some (cfg true [] ys) := by
  simp [FinTM2.step,appendProgram,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_one (ys : List Bool) : appendProgram.machine.step (cfg false [true] ys)=some (cfg true [] ys) := by
  simp [FinTM2.step,appendProgram,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_false (xs ys : List Bool) : appendProgram.machine.step (cfg false (false::xs) ys)=some (cfg true xs ys) := by
  simp [FinTM2.step,appendProgram,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_true (b : Bool) (xs ys : List Bool) :
    appendProgram.machine.step (cfg false (true::b::xs) ys)=some (cfg false xs (b::ys)) := by
  simp [FinTM2.step,appendProgram,cfg,TM2.step,TM2.stepAux,upd0,upd1]; rfl
lemma restore_nil (xs : List Bool) : appendProgram.machine.step (cfg true xs [])=some (done xs) := by
  simp [FinTM2.step,appendProgram,cfg,done,TM2.step,TM2.stepAux,upd1]; rfl
lemma restore_cons (b : Bool) (xs ys : List Bool) :
    appendProgram.machine.step (cfg true xs (b::ys))=some (cfg true (b::xs) ys) := by
  simp [FinTM2.step,appendProgram,cfg,TM2.step,TM2.stepAux,upd0,upd1]; rfl

noncomputable def parse_phase (xs ys : List Bool) :
    EvalsToInTime appendProgram.machine.step (cfg false xs ys)
      (some (cfg true (discardPrefix xs) ((extractPrefix xs).reverse++ys))) (xs.length+1) := by
  induction xs using List.twoStepInduction generalizing ys with
  | nil => exact one_step (parse_nil ys)
  | singleton b =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_singleton] using
        time_mono (one_step (parse_false [] ys)) (by decide : 1≤2)
    | true => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_singleton] using
        time_mono (one_step (parse_one ys)) (by decide : 1≤2)
  | cons_cons b c xs ih _ =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append] using
        time_mono (one_step (parse_false (c::xs) ys)) (by simp : 1≤(false::c::xs).length+1)
    | true =>
      have hh := step_then (parse_true c xs ys) (ih (c::ys))
      simp only [extractPrefix,discardPrefix,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp)

noncomputable def restore_phase (xs ys : List Bool) :
    EvalsToInTime appendProgram.machine.step (cfg true xs ys)
      (some (done (ys.reverse++xs))) (ys.length+1) := by
  induction ys generalizing xs with
  | nil => exact one_step (restore_nil xs)
  | cons b ys ih =>
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using step_then (restore_cons b xs ys) (ih (b::xs))

lemma initial (xs : List Bool) : initList appendProgram.machine xs=cfg false xs [] := by
  rw [initList_bool]
  congr 1
  funext i; fin_cases i <;> simp [appendProgram,store]
lemma final (xs : List Bool) : haltList appendProgram.machine xs=done xs := by
  rw [haltList_bool]
  congr 1
  funext i; fin_cases i <;> simp [appendProgram,store]

noncomputable def append_computes : PolyComputes (fun xs=>extractPrefix xs++discardPrefix xs) where
  program := appendProgram
  time := 2*Polynomial.X+2
  outputs xs := by
    have h1 := parse_phase xs []
    have h2 := restore_phase (discardPrefix xs) (extractPrefix xs).reverse
    simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h1 h2
    have hh := eval_trans h1 h2
    simp only [TM2OutputsInTime,Option.map_some,initial,final,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    have hl := extractPrefix_length xs
    exact time_mono hh (by omega)

abbrev tailProgram : Program where
  K := Unit
  input := ()
  output := ()
  Label := Unit
  main := ()
  State := Unit
  initial := ()
  code _ := .pop () (fun _ _=>()) .halt

noncomputable def tail_computes : PolyComputes (List.tail : List Bool → List Bool) where
  program := tailProgram
  time := 1
  outputs xs := by
    simp only [TM2OutputsInTime,Option.map_some,Polynomial.eval_one]
    apply one_step
    cases xs <;> simp [initList_bool,haltList_bool,FinTM2.step,tailProgram,TM2.step,TM2.stepAux,unit_update]
    all_goals rfl

end WordOperations

noncomputable def PolyComputes.append {f g : List Bool → List Bool}
    (hf : PolyComputes f) (hg : PolyComputes g) : PolyComputes (fun xs=>f xs++g xs) := by
  have hh := (hf.pair hg).comp WordOperations.append_computes
  simpa only [Function.comp_def,pairBits,extractPrefix_pair,discardPrefix_pair] using hh

noncomputable def const_computes (ys : List Bool) : PolyComputes (fun _=>ys) := by
  have hh := FiniteFold.computes () (fun _ _=>()) (fun _=>ys)
  exact hh

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Computes
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.discardPrefix_pairBits _root_.OAI.MetricKMedianRecovery.BitMachine.extractPrefix_pairBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open Turing Turing.TM2 StateTransition
namespace WordSelection
open WordOperations

abbrev program : Program where
  K := Fin 2
  input := 0
  output := 0
  Label := Fin 5
  main := 0
  State := Option Bool
  initial := none
  code l := if l=0 then
    .pop 0 (fun _ b=>b)
      (.branch (fun s=>decide (s=some true))
        (.load (fun _=>none) (.goto (fun _=>1)))
        (.load (fun _=>none) (.goto (fun _=>2))))
    else if l=1 then
      .pop 0 (fun _ b=>b)
        (.branch (fun s=>decide (s=some true))
          (.pop 0 (fun _ b=>b)
            (.branch Option.isSome
              (.push 1 (fun s=>s.getD false) (.load (fun _=>none) (.goto (fun _=>1))))
              (.load (fun _=>none) (.goto (fun _=>3)))))
          (.load (fun _=>none) (.goto (fun _=>3))))
    else if l=2 then
      .pop 0 (fun _ b=>b)
        (.branch (fun s=>decide (s=some true))
          (.pop 0 (fun _ b=>b)
            (.branch Option.isSome
              (.load (fun _=>none) (.goto (fun _=>2)))
              (.load (fun _=>none) .halt)))
          (.load (fun _=>none) .halt))
    else if l=3 then
      .pop 0 (fun _ b=>b)
        (.branch Option.isSome
          (.load (fun _=>none) (.goto (fun _=>3)))
          (.load (fun _=>none) (.goto (fun _=>4))))
    else
      .pop 1 (fun _ b=>b)
        (.branch Option.isSome
          (.push 0 (fun s=>s.getD false) (.load (fun _=>none) (.goto (fun _=>4))))
          (.load (fun _=>none) .halt))

def cfg (l : Fin 5) (xs ys : List Bool) : program.machine.Cfg := ⟨some l,none,store xs ys⟩
def done (xs : List Bool) : program.machine.Cfg := ⟨none,none,store xs []⟩

lemma start_true (xs : List Bool) : program.machine.step (cfg 0 (true::xs) [])=some (cfg 1 xs []) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma start_false (xs : List Bool) : program.machine.step (cfg 0 (false::xs) [])=some (cfg 2 xs []) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma start_nil : program.machine.step (cfg 0 [] [])=some (cfg 2 [] []) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_nil (ys : List Bool) : program.machine.step (cfg 1 [] ys)=some (cfg 3 [] ys) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_one (ys : List Bool) : program.machine.step (cfg 1 [true] ys)=some (cfg 3 [] ys) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_false (xs ys : List Bool) : program.machine.step (cfg 1 (false::xs) ys)=some (cfg 3 xs ys) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma parse_true (b : Bool) (xs ys : List Bool) :
    program.machine.step (cfg 1 (true::b::xs) ys)=some (cfg 1 xs (b::ys)) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0,upd1]; rfl
lemma discard_nil : program.machine.step (cfg 2 [] [])=some (done []) := by
  simp [FinTM2.step,program,cfg,done,TM2.step,TM2.stepAux,upd0]; rfl
lemma discard_one : program.machine.step (cfg 2 [true] [])=some (done []) := by
  simp [FinTM2.step,program,cfg,done,TM2.step,TM2.stepAux,upd0]; rfl
lemma discard_false (xs : List Bool) : program.machine.step (cfg 2 (false::xs) [])=some (done xs) := by
  simp [FinTM2.step,program,cfg,done,TM2.step,TM2.stepAux,upd0]; rfl
lemma discard_true (b : Bool) (xs : List Bool) :
    program.machine.step (cfg 2 (true::b::xs) [])=some (cfg 2 xs []) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma clear_nil (ys : List Bool) : program.machine.step (cfg 3 [] ys)=some (cfg 4 [] ys) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma clear_cons (b : Bool) (xs ys : List Bool) : program.machine.step (cfg 3 (b::xs) ys)=some (cfg 3 xs ys) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0]; rfl
lemma restore_nil (xs : List Bool) : program.machine.step (cfg 4 xs [])=some (done xs) := by
  simp [FinTM2.step,program,cfg,done,TM2.step,TM2.stepAux,upd1]; rfl
lemma restore_cons (b : Bool) (xs ys : List Bool) : program.machine.step (cfg 4 xs (b::ys))=some (cfg 4 (b::xs) ys) := by
  simp [FinTM2.step,program,cfg,TM2.step,TM2.stepAux,upd0,upd1]; rfl

noncomputable def parse_phase (xs ys : List Bool) :
    EvalsToInTime program.machine.step (cfg 1 xs ys)
      (some (cfg 3 (discardPrefix xs) ((extractPrefix xs).reverse++ys))) (xs.length+1) := by
  induction xs using List.twoStepInduction generalizing ys with
  | nil => exact one_step (parse_nil ys)
  | singleton b =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_singleton] using
        time_mono (one_step (parse_false [] ys)) (by decide : 1≤2)
    | true => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_singleton] using
        time_mono (one_step (parse_one ys)) (by decide : 1≤2)
  | cons_cons b c xs ih _ =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append] using
        time_mono (one_step (parse_false (c::xs) ys)) (by simp : 1≤(false::c::xs).length+1)
    | true =>
      have hh := step_then (parse_true c xs ys) (ih (c::ys))
      simp only [extractPrefix,discardPrefix,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp)

noncomputable def restore_phase (xs ys : List Bool) :
    EvalsToInTime program.machine.step (cfg 4 xs ys)
      (some (done (ys.reverse++xs))) (ys.length+1) := by
  induction ys generalizing xs with
  | nil => exact one_step (restore_nil xs)
  | cons b ys ih =>
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using step_then (restore_cons b xs ys) (ih (b::xs))

noncomputable def discard_phase (xs : List Bool) :
    EvalsToInTime program.machine.step (cfg 2 xs []) (some (done (discardPrefix xs))) (xs.length+1) := by
  induction xs using List.twoStepInduction with
  | nil => exact one_step discard_nil
  | singleton b =>
    cases b with
    | false => simpa only [discardPrefix,List.length_singleton] using
        time_mono (one_step (discard_false [])) (by decide : 1≤2)
    | true => simpa only [discardPrefix,List.length_singleton] using
        time_mono (one_step discard_one) (by decide : 1≤2)
  | cons_cons b c xs ih _ =>
    cases b with
    | false => simpa only [discardPrefix] using
        time_mono (one_step (discard_false (c::xs))) (by simp : 1≤(false::c::xs).length+1)
    | true =>
      have hh := step_then (discard_true c xs) ih
      simp only [discardPrefix]
      exact time_mono hh (by simp)

noncomputable def clear_phase (xs ys : List Bool) :
    EvalsToInTime program.machine.step (cfg 3 xs ys) (some (cfg 4 [] ys)) (xs.length+1) := by
  induction xs with
  | nil => exact one_step (clear_nil ys)
  | cons b xs ih => simpa only [List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
        (step_then (clear_cons b xs ys) ih)

noncomputable def true_phase (xs : List Bool) :
    EvalsToInTime program.machine.step (cfg 1 xs []) (some (done (extractPrefix xs))) (3*xs.length+3) := by
  have h1 := parse_phase xs []
  have h2 := clear_phase (discardPrefix xs) (extractPrefix xs).reverse
  have h3 := restore_phase [] (extractPrefix xs).reverse
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h1 h3
  have hh := eval_trans h1 (eval_trans h2 h3)
  have hl := ProductBits.projections_length xs
  exact time_mono hh (by omega)

noncomputable def outputs (xs : List Bool) :
    EvalsToInTime program.machine.step (cfg 0 xs []) (some (done (choose xs))) (4*xs.length+4) := by
  cases xs with
  | nil =>
    have hh := step_then start_nil (one_step discard_nil)
    exact time_mono hh (by decide : 2≤4)
  | cons b xs =>
    cases b with
    | false =>
      have hh := step_then (start_false xs) (discard_phase xs)
      simpa only [choose,List.head?_cons,List.tail_cons,Option.some.injEq,Bool.false_eq_true,ite_false, if_false] using
        time_mono hh (by simp only [List.length_cons]; omega)
    | true =>
      have hh := step_then (start_true xs) (true_phase xs)
      simpa only [choose,List.head?_cons,List.tail_cons,ite_true, if_true] using
        time_mono hh (by simp only [List.length_cons]; omega)

lemma initial (xs : List Bool) : initList program.machine xs=cfg 0 xs [] := by
  rw [initList_bool]
  congr 1
  funext i; fin_cases i <;> simp [program,store]
lemma final (xs : List Bool) : haltList program.machine xs=done xs := by
  rw [haltList_bool]
  congr 1
  funext i; fin_cases i <;> simp [program,store]

noncomputable def choose_computes : PolyComputes choose where
  program := program
  time := 4*Polynomial.X+4
  outputs xs := by
    simpa only [TM2OutputsInTime,Option.map_some,initial,final,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X] using outputs xs

end WordSelection

noncomputable def PolyComputes.cond {p : List Bool → Bool} {f g : List Bool → List Bool}
    (hp : PolyComputes (fun xs=>[p xs])) (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun xs=>if p xs then f xs else g xs) := by
  have hh := (hp.append (hf.pair hg)).comp WordSelection.choose_computes
  simpa only [Function.comp_def,List.singleton_append,WordSelection.choose,List.head?_cons,
    List.tail_cons,Option.some.injEq,pairBits,extractPrefix_pair,discardPrefix_pair] using hh

noncomputable def id_computes : PolyComputes id := by
  have he : (List.reverse ∘ List.reverse : List Bool → List Bool) = id := by
    funext x
    exact List.reverse_reverse x
  rw [← he]
  exact reverse_computes.comp reverse_computes

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

noncomputable def pack_computes {c d o : List Bool → List Bool} (a : Bool)
    (hc : PolyComputes c) (hd : PolyComputes d) (ho : PolyComputes o) :
    PolyComputes (fun x=>pack a (c x) (d x) (o x)) :=
  (const_computes [a]).append (hc.pair (hd.pair ho))

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations UnaryTake
namespace PolynomialCounter
noncomputable def constant (n : ℕ) : PolynomialCounter (Polynomial.C n) where
  word _ := List.replicate n false
  computes := const_computes (List.replicate n false)
  word_length x := by simp only [List.length_replicate,Polynomial.eval_C]
noncomputable def identity : PolynomialCounter Polynomial.X where
  word := id
  computes := id_computes
  word_length x := by simp only [id_eq,Polynomial.eval_X]
noncomputable def add {P Q : Polynomial ℕ} (p : PolynomialCounter P) (q : PolynomialCounter Q) :
    PolynomialCounter (P+Q) where
  word x := p.word x++q.word x
  computes := p.computes.append q.computes
  word_length x := by simp only [List.length_append,p.word_length,q.word_length,Polynomial.eval_add]
end PolynomialCounter

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

def coefInflate (x : List Bool) : List Bool := BinaryRational.encode (1/(1-1/(8*dimension x^2)))
end BinaryEllipsoidCut
end MetricKMedianRecovery.BitMachine

end OAI
end


