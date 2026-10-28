-- Prove2me | Definitions.Def_OAIQ035K027
-- name    : OAIQ035K027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:58:27.43812+00:00
-- url     : https://prove2.me/theorems/879f69d6-686c-4b5e-9b96-f6a397b559bd
-- title:
--   Definitions bundle OAIQ035K027 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 75 declarations of OpenAI's Lean: 50 definitions, 1 instance and 24 theorems. The definitions and types are `OAI.MetricKMedian.Binary.AdditionLoop.loop`, `OAI.MetricKMedian.Binary.AdditionLoop.program`, `OAI.MetricKMedian.Binary.ListFold.loop`, `OAI.MetricKMedian.Binary.ListFold.program`, `OAI.MetricKMedian.Binary.ListReverse.loop`, `OAI.MetricKMedian.Binary.ListReverse.program`, `OAI.MetricKMedian.Binary.Loop.auxiliary`, `OAI.MetricKMedian.Binary.Loop.body`, `OAI.MetricKMedian.Binary.Loop.check`, `OAI.MetricKMedian.Binary.Loop.checkCfg`, `OAI.MetricKMedian.Binary.Loop.checkCode`, `OAI.MetricKMedian.Binary.Loop.clean`, `OAI.MetricKMedian.Binary.Loop.code`, `OAI.MetricKMedian.Binary.Loop.following`, `OAI.MetricKMedian.Binary.Loop.machine`, `OAI.MetricKMedian.Binary.Loop.phase`, `OAI.MetricKMedian.Binary.Loop.source`, `OAI.MetricKMedian.Binary.Loop.target`, `OAI.MetricKMedian.Binary.Loop.transfer`, `OAI.MetricKMedian.Binary.Loop.transferCfg`, `OAI.MetricKMedian.Binary.MultiplicationLoop.program`, `OAI.MetricKMedian.Binary.PolyProgram.addWords`, `OAI.MetricKMedian.Binary.PolyProgram.fanout`, `OAI.MetricKMedian.Binary.PolyProgram.intAdd`, `OAI.MetricKMedian.Binary.PolyProgram.intFromParts`, `OAI.MetricKMedian.Binary.PolyProgram.intOfNat`, `OAI.MetricKMedian.Binary.PolyProgram.ite`, `OAI.MetricKMedian.Binary.PolyProgram.listFold`, `OAI.MetricKMedian.Binary.PolyProgram.listHead`, `OAI.MetricKMedian.Binary.PolyProgram.listMapWith`, `OAI.MetricKMedian.Binary.PolyProgram.listReverse`, `OAI.MetricKMedian.Binary.PolyProgram.listTail`, `OAI.MetricKMedian.Binary.PolyProgram.listUncons`, `OAI.MetricKMedian.Binary.PolyProgram.loop`, `OAI.MetricKMedian.Binary.PolyProgram.natAdd`, `OAI.MetricKMedian.Binary.PolyProgram.natBit`, `OAI.MetricKMedian.Binary.PolyProgram.natLT`, `OAI.MetricKMedian.Binary.PolyProgram.natSub`, `OAI.MetricKMedian.Binary.PolyProgram.normalize`, `OAI.MetricKMedian.Binary.PolyProgram.product` and 10 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Binary_BinaryAddition`, `KMedian_Binary_BinaryAutomatic`, `KMedian_Binary_BinaryInteger`, `KMedian_Binary_BinaryListContext`, `KMedian_Binary_BinaryListFold`, `KMedian_Binary_BinaryLists`, `KMedian_Binary_BinaryMultiplication`, `KMedian_Binary_BinaryNatural`, `KMedian_Binary_BinarySubtraction`, `KMedian_Binary_BinaryWords`, `KMedian_Binary_BooleanListPrimitives`, `KMedian_Binary_BooleanLoop`, `KMedian_Binary_BooleanProducts`, `KMedian_Binary_BooleanReverse`, `KMedian_Binary_BooleanThread`, `KMedian_Geometry_GraphListOperations`.
--
--   **Imports.** It imports the bundles `OAIQ035K013` and `OAIQ035K014` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K038`, `OAIQ035K039`, `OAIQ035K040`, `OAIQ035K041`, `OAIQ035K043` and `OAIQ035K062`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K013
import Definitions.Def_OAIQ035K014

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace Loop
variable (M : Machine)
abbrev auxiliary : Key M := .inr ()
abbrev check : Label M := .inr none
abbrev phase (b : Bool) : Label M := .inr (some b)

def body : Embedding M.K M.Label M.State (Key M) (Label M) (State M) where
  key := Sum.inl
  read := Prod.fst
  write v x := (x,v.2)
  state v := (v,none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := Sum.elim s (fun _ => [])
  stack_key _ _ := rfl
  stack_update s k x := by
    funext j
    rcases j with j | j <;>
      simp only [update_apply,Sum.elim_inl,Sum.elim_inr,Sum.inl.injEq,Sum.inr_ne_inl,ite_false]
  label := Sum.inl
  halted := some (check M)
  stop := .goto (fun _ => check M)
  stop_spec _ _ := rfl

def source (b : Bool) : Key M := if b then auxiliary M else .inl M.output

def target (b : Bool) : Key M := if b then .inl M.input else auxiliary M

 theorem source_ne_target (b : Bool) : source M b ≠ target M b := by
  cases b <;> simp [source,target,auxiliary]

def following (b : Bool) : Label M := if b then .inl M.main else phase M true

def clean (v : State M) : State M := (v.1,none)

def transfer (b : Bool) : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (source M b) (fun v c => (v.1,c))
    (.branch (fun v => v.2.isSome)
      (.push (target M b) (fun v => v.2.getD false)
        (.load (clean M) (.goto (fun _ => phase M b))))
      (.load (clean M) (.goto (fun _ => following M b))))

def checkCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (.inl M.output) (fun v c => (v.1,c))
    (.branch (fun v => v.2.getD false)
      (.load (clean M) (.goto (fun _ => phase M false)))
      (.load (clean M) .halt))

def code : Label M → TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M)
  | .inl l => (body M).stmt (M.code l)
  | .inr none => checkCode M
  | .inr (some b) => transfer M b

abbrev machine : Machine where
  K := Key M
  input := .inl M.input
  output := .inl M.output
  Label := Label M
  main := .inl M.main
  State := State M
  initial := (M.initial,none)
  code := code M

 theorem code_body (l : M.Label) : (machine M).code ((body M).label l)=
    (body M).stmt (M.code l) := rfl

 theorem initial_body (s : List Bool) : (body M).cfg (M.initialCfg s)=
    (machine M).initialCfg s := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [Embedding.cfg,body,Machine.initialCfg]

def transferCfg (b : Bool) (xs ys : List Bool) : (machine M).Cfg :=
  ⟨some (phase M b),(M.initial,none),twoStacks (source M b) (target M b) xs ys⟩

 theorem transfer_cons (b x : Bool) (xs ys : List Bool) :
    (machine M).step (transferCfg M b (x::xs) ys)=some (transferCfg M b xs (x::ys)) := by
  change some (TM2.stepAux (transfer M b) (M.initial,none)
    (twoStacks (source M b) (target M b) (x::xs) ys))=_
  simp only [transfer,TM2.stepAux]
  rw [twoStacks_source]
  simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,Option.getD_some,clean]
  rw [update_of_ne (Ne.symm (source_ne_target M b)),twoStacks_target (source_ne_target M b)]
  rw [twoStacks_move (source_ne_target M b)]
  rfl

 theorem transfer_run (b : Bool) (xs ys : List Bool) :
    Trace (machine M).step xs.length (transferCfg M b xs ys)
      (transferCfg M b [] (xs.reverse++ys)) := by
  induction xs generalizing ys with
  | nil => exact Trace.refl _
  | cons x xs ih =>
      have h := Trace.cons (transfer_cons M b x xs ys) (ih (x::ys))
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using h

 theorem transfer_empty (b : Bool) (ys : List Bool) :
    (machine M).step (transferCfg M b [] ys)=
      some ⟨some (following M b),(M.initial,none),twoStacks (source M b) (target M b) [] ys⟩ := by
  change some (TM2.stepAux (transfer M b) (M.initial,none)
    (twoStacks (source M b) (target M b) [] ys))=_
  simp only [transfer,TM2.stepAux]
  rw [twoStacks_source]
  simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false,clean,twoStacks_pop_empty]

 theorem transfer_change (ys : List Bool) :
    (machine M).step (transferCfg M false [] ys)=some (transferCfg M true ys []) := by
  rw [transfer_empty]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [transferCfg,source,target,twoStacks,auxiliary]

 theorem transfer_end (ys : List Bool) :
    (machine M).step (transferCfg M true [] ys)=some ((machine M).initialCfg ys) := by
  rw [transfer_empty]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [Machine.initialCfg,source,target,twoStacks,auxiliary]

 theorem transfer_full (xs : List Bool) :
    Trace (machine M).step (2*xs.length+2) (transferCfg M false xs []) ((machine M).initialCfg xs) := by
  have h₁ := transfer_run M false xs []
  simp only [List.append_nil] at h₁
  have h₂ := Trace.cons (transfer_change M xs.reverse) (transfer_run M true xs.reverse [])
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at h₂
  have h₃ := Trace.cons (transfer_end M xs) (Trace.refl _)
  have hh := (h₁.trans h₂).trans h₃
  simpa only [show xs.length+(xs.length+1)+(0+1)=2*xs.length+2 by omega] using hh

def checkCfg (xs : List Bool) : (machine M).Cfg :=
  ⟨some (check M),(M.initial,none),fun k => if k=Sum.inl M.output then xs else []⟩

 theorem body_final (xs : List Bool) : (body M).cfg (M.finalCfg xs)=checkCfg M xs := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [body,Embedding.cfg,Machine.finalCfg,checkCfg]

 theorem check_step (b : Bool) (xs : List Bool) :
    (machine M).step (checkCfg M (b::xs))=
      some ⟨if b then some (phase M false) else none,(M.initial,none),
        fun k => if k=Sum.inl M.output then xs else []⟩ := by
  change some (TM2.stepAux (checkCode M) (M.initial,none)
    (fun k => if k=Sum.inl M.output then b::xs else []))=_
  simp only [checkCode,TM2.stepAux,List.head?_cons,List.tail_cons,
    Option.getD_some,clean,ite_true]
  cases b <;> simp only [Bool.cond_false,Bool.cond_true,Bool.false_eq_true,ite_false,ite_true]
  all_goals
    apply congrArg some
    apply cfg_ext <;> try rfl
    funext k
    by_cases h : k=Sum.inl M.output <;> simp [h]

 theorem check_false (xs : List Bool) :
    (machine M).step ((body M).cfg (M.finalCfg (false::xs)))=some ((machine M).finalCfg xs) := by
  rw [body_final,check_step]
  rfl

 theorem check_true (xs : List Bool) :
    (machine M).step ((body M).cfg (M.finalCfg (true::xs)))=some (transferCfg M false xs []) := by
  rw [body_final,check_step]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [transferCfg,twoStacks,source,target,auxiliary]

 theorem stop {s t : List Bool} {n : ℕ}
    (hM : Trace M.step n (M.initialCfg s) (M.finalCfg (false::t))) :
    Trace (machine M).step (n+1) ((machine M).initialCfg s) ((machine M).finalCfg t) := by
  have h := (body M).trace M.code (machine M).code (code_body M) hM
  rw [initial_body] at h
  exact h.trans (Trace.cons (check_false M t) (Trace.refl _))

 theorem next {s t u : List Bool} {n m : ℕ}
    (hM : Trace M.step n (M.initialCfg s) (M.finalCfg (true::t)))
    (hR : Trace (machine M).step m ((machine M).initialCfg t) ((machine M).finalCfg u)) :
    Trace (machine M).step (n+2*t.length+3+m) ((machine M).initialCfg s) ((machine M).finalCfg u) := by
  have h := (body M).trace M.code (machine M).code (code_body M) hM
  rw [initial_body] at h
  have hg := Trace.cons (check_true M t) (transfer_full M t)
  have hh := (h.trans hg).trans hR
  simpa only [Nat.add_assoc,show 2*t.length+2+1=2*t.length+3 by omega] using hh

end Loop

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
variable {f : α → β ⊕ α}

 theorem run_loop (P : PolyProgram ea (encodeLoop ea eb) f) {S n : ℕ} {a : α} {b : β}
    (h : BoundedRun ea f S n a b) :
    ∃ t ≤ n*P.passTime S, Trace (Loop.machine P.machine).step t
      ((Loop.machine P.machine).initialCfg (ea a)) ((Loop.machine P.machine).finalCfg (eb b)) := by
  induction h with
  | @stop a b ha hab =>
      have hp := P.outputs a
      have ht : Trace P.machine.step hp.steps (P.machine.initialCfg (ea a))
          (P.machine.finalCfg (false::eb b)) := by
        have hh : Trace P.machine.step hp.steps (P.machine.initialCfg (ea a))
            (P.machine.finalCfg (encodeLoop ea eb (f a))) := Trace.of_iterate hp.evals_in_steps
        simpa only [hab,encodeLoop] using hh
      refine ⟨hp.steps+1,?_,Loop.stop P.machine ht⟩
      have htime := hp.steps_le_m.trans (polynomial_eval_mono P.time ha)
      simp only [passTime,one_mul]
      omega
  | @step a a' b n ha haa' h ih =>
      obtain ⟨t,ht,htrace⟩ := ih
      have hp := P.outputs a
      have hb : Trace P.machine.step hp.steps (P.machine.initialCfg (ea a))
          (P.machine.finalCfg (true::ea a')) := by
        have hh : Trace P.machine.step hp.steps (P.machine.initialCfg (ea a))
            (P.machine.finalCfg (encodeLoop ea eb (f a))) := Trace.of_iterate hp.evals_in_steps
        simpa only [haa',encodeLoop] using hh
      refine ⟨hp.steps+2*(ea a').length+3+t,?_,Loop.next P.machine hb htrace⟩
      have htime := hp.steps_le_m.trans (polynomial_eval_mono P.time ha)
      have hl := (P.length_bound a).trans (polynomial_eval_mono P.sizeBound ha)
      simp only [haa',encodeLoop,List.length_cons] at hl
      dsimp only [passTime] at ht ⊢
      rw [Nat.add_mul]
      omega

noncomputable def loop (P : PolyProgram ea (encodeLoop ea eb) f) (g : α → β)
    (iterations sizes : Polynomial ℕ)
    (h : ∀ a, ∃ n ≤ iterations.eval (ea a).length,
      BoundedRun ea f (sizes.eval (ea a).length) n a (g a)) : PolyProgram ea eb g where
  machine := Loop.machine P.machine
  time := iterations*(P.time.comp sizes+2*P.sizeBound.comp sizes+3)
  outputs a := Classical.choice (show Nonempty _ from by
    obtain ⟨n,hn,hrun⟩ := h a
    obtain ⟨t,ht,htrace⟩ := P.run_loop hrun
    refine ⟨⟨⟨t,htrace.iterate_eq⟩,?_⟩⟩
    refine ht.trans ?_
    simpa only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_comp,
      Polynomial.eval_ofNat,passTime] using Nat.mul_le_mul_right (P.passTime (sizes.eval (ea a).length)) hn)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanThread
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool} {f : α → β}

 noncomputable def thread (P : PolyProgram ea eb f) (ec : γ → List Bool) :
    PolyProgram (encodePair ea ec) (encodePair eb ec) (fun x => (f x.1,x.2)) where
  machine := Thread.machine P.machine
  time := 2*X+3*P.sizeBound+5+P.time
  outputs x := by
    have hp := P.outputs x.1
    have h := Thread.run P.machine (ec x.2) (Trace.of_iterate hp.evals_in_steps)
    refine ⟨⟨_,h.iterate_eq⟩,?_⟩
    have hn : (ea x.1).length≤(encodePair ea ec x).length := by simp only [encodePair_length]; omega
    have hl := (P.length_bound x.1).trans (polynomial_eval_mono P.sizeBound hn)
    have ht := hp.steps_le_m.trans (polynomial_eval_mono P.time hn)
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    omega

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace PolyProgram
variable {α β γ δ : Type}
variable {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool} {ed : δ → List Bool}
variable {f : α → β} {g : γ → δ}

noncomputable def second (P : PolyProgram ea eb f) (ec : γ → List Bool) :
    PolyProgram (encodePair ec ea) (encodePair ec eb) (fun x => (x.1,f x.2)) :=
  (((exchange ec ea).comp (P.thread ec)).comp (exchange eb ec)).congr _ (fun _ => rfl)

noncomputable def product (P : PolyProgram ea eb f) (Q : PolyProgram ec ed g) :
    PolyProgram (encodePair ea ec) (encodePair eb ed) (fun x => (f x.1,g x.2)) :=
  ((P.thread ec).comp (Q.second eb)).congr _ (fun _ => rfl)

noncomputable def fanout {h : α → γ} (P : PolyProgram ea eb f) (Q : PolyProgram ea ec h) :
    PolyProgram ea (encodePair eb ec) (fun a => (f a,h a)) :=
  ((duplicate ea).comp (P.product Q)).congr _ (fun _ => rfl)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanListPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}

noncomputable def ite {p : α → Bool} {f g : α → β}
    (P : PolyProgram ea encodeBool p) (F : PolyProgram ea eb f) (G : PolyProgram ea eb g) :
    PolyProgram ea eb (fun a => if p a then g a else f a) :=
  ((P.fanout (F.fanout G)).comp (select eb)).congr _ (fun _ => rfl)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanReverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace ReverseLoop

noncomputable def program : PolyProgram enc (encodeLoop enc id) body := by
  let first := PolyProgram.fst id id
  let last := PolyProgram.snd id id
  let hd := first.comp PolyProgram.head
  let tl := first.comp PolyProgram.tail
  let newLast := (hd.fanout last).comp PolyProgram.cons
  let recur := (tl.fanout newLast).comp (PolyProgram.injectRight enc id)
  let done := last.comp (PolyProgram.injectLeft enc id)
  exact (PolyProgram.ite (first.comp PolyProgram.isEmpty) recur done).congr _ (fun _ => rfl)

noncomputable def loop : PolyProgram enc id result :=
  program.loop result (X+1) X (fun s => by
    refine ⟨s.1.length+1,?_,?_⟩
    · simp only [eval_add,eval_X,eval_one,enc,encodePair_length,id_eq]; omega
    · simpa only [eval_X,enc,encodePair_length,id_eq,result] using run s.1 s.2 (2*s.1.length+1+s.2.length) le_rfl)

end ReverseLoop

namespace PolyProgram
noncomputable def reverse : PolyProgram id id List.reverse :=
  (((identity id).fanout (constant id id [])).comp ReverseLoop.loop).congr _
    (fun _ => List.append_nil _)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace PolyProgram

noncomputable def normalize : PolyProgram id id Word.normalize :=
  ((reverse.comp dropFalse).comp reverse).congr _ (fun _ => rfl)

noncomputable def toBits : PolyProgram id Nat.bits Word.value :=
  normalize.of_word (fun xs => Word.normalize_eq_bits xs)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryAddition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace AdditionLoop

noncomputable def program : PolyProgram enc (encodeLoop enc id) body := by
  let px := PolyProgram.fst id ey
  let pyz := PolyProgram.snd id ey
  let py := pyz.comp (PolyProgram.fst id ec)
  let pca := pyz.comp (PolyProgram.snd id ec)
  let pc := pca.comp (PolyProgram.fst encodeBool id)
  let pa := pca.comp (PolyProgram.snd encodeBool id)
  let bits := (px.comp PolyProgram.head).fanout ((py.comp PolyProgram.head).fanout pc)
  let binj := encodePair_injective encodeBool_injective (encodePair_injective encodeBool_injective encodeBool_injective)
  let sb := bits.comp (PolyProgram.boolFunction _ encodeBool (fun v : Bool × (Bool × Bool) => Word.sumBit v.1 v.2.1 v.2.2) binj)
  let cb := bits.comp (PolyProgram.boolFunction _ encodeBool (fun v : Bool × (Bool × Bool) => Word.carryBit v.1 v.2.1 v.2.2) binj)
  let na := (sb.fanout pa).comp PolyProgram.cons
  let pn := (px.comp PolyProgram.tail).fanout ((py.comp PolyProgram.tail).fanout (cb.fanout na))
  let pe := ((px.comp PolyProgram.isEmpty).fanout (py.comp PolyProgram.isEmpty)).comp PolyProgram.boolAnd
  let pf := (PolyProgram.ite pc pa ((PolyProgram.constant enc encodeBool true).fanout pa |>.comp PolyProgram.cons)).comp PolyProgram.reverse
  exact (PolyProgram.ite pe (pn.comp (PolyProgram.injectRight enc id))
    (pf.comp (PolyProgram.injectLeft enc id))).congr _ (fun _ => rfl)

noncomputable def loop : PolyProgram enc id result :=
  program.loop result (X+1) X (fun s => by
    obtain ⟨n,hn,hr⟩ := run (s.1.length+s.2.1.length) s (enc s).length rfl le_rfl
    refine ⟨n,?_,?_⟩
    · simp only [eval_add,eval_X,eval_one,enc_length]; omega
    · simpa only [eval_X] using hr)

end AdditionLoop

namespace PolyProgram
noncomputable def addWords : PolyProgram (encodePair id id) id (fun x : List Bool × List Bool => Word.add x.1 x.2 false) := by
  let ex : List Bool × List Bool → List Bool := encodePair id id
  let init := (fst id id).fanout ((snd id id).fanout (constant ex AdditionLoop.ec (false,[])))
  exact (init.comp AdditionLoop.loop).congr _ (fun _ => rfl)

noncomputable def natAdd : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1+x.2) :=
  (addWords.comp toBits).recode (fun x => (x.1.bits,x.2.bits)) (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,Word.value_add,Word.value_bits,Bool.toNat_false,Nat.add_zero])
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)

noncomputable def listUncons : PolyProgram (encodeList ea) (encodePair ea (encodeList ea))
    (fun as => (as.head?.getD a0,as.tail)) := by
  let raw : PolyProgram (encodeList ea) id (encodeList ea) := (identity id).recode (encodeList ea) (fun _ => rfl) (fun _ => rfl)
  let deflt := constant (encodeList ea) id (Binary.quote (ea a0))
  refine (ite (listIsEmpty ea) raw deflt).recode id (fun _ => rfl) ?_
  intro as
  cases as with
  | nil => simp [encodePair,encodeList]
  | cons a as => rfl
noncomputable def listHead : PolyProgram (encodeList ea) ea (fun as => as.head?.getD a0) :=
  ((listUncons ea a0).comp (fst ea (encodeList ea))).congr _ (fun _ => rfl)
noncomputable def listTail : PolyProgram (encodeList ea) (encodeList ea) List.tail :=
  ((listUncons ea a0).comp (snd ea (encodeList ea))).congr _ (fun _ => rfl)
end PolyProgram

namespace ListReverse
variable {α : Type} (ea : α → List Bool) (a0 : α)

noncomputable def program : PolyProgram (enc ea) (encodeLoop (enc ea) (encodeList ea)) (body a0) := by
  let px := PolyProgram.fst (encodeList ea) (encodeList ea)
  let py := PolyProgram.snd (encodeList ea) (encodeList ea)
  let hd := px.comp (PolyProgram.listHead ea a0)
  let tl := px.comp (PolyProgram.listTail ea a0)
  let newLast := (hd.fanout py).comp (PolyProgram.listCons ea)
  let recur := (tl.fanout newLast).comp (PolyProgram.injectRight (enc ea) (encodeList ea))
  let done := py.comp (PolyProgram.injectLeft (enc ea) (encodeList ea))
  exact (PolyProgram.ite (px.comp (PolyProgram.listIsEmpty ea)) recur done).congr _ (fun _ => rfl)

noncomputable def loop : PolyProgram (enc ea) (encodeList ea) result :=
  (program ea a0).loop result (X+1) X (fun s => by
    refine ⟨s.1.length+1,?_,?_⟩
    · have h := EncodedList.length_le ea s.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]; omega
    · simpa only [eval_X,enc,encodePair_length,result] using run ea a0 s.1 s.2
        (2*(encodeList ea s.1).length+1+(encodeList ea s.2).length) le_rfl)
end ListReverse

namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listReverse : PolyProgram (encodeList ea) (encodeList ea) List.reverse :=
  (((identity (encodeList ea)).fanout (constant (encodeList ea) (encodeList ea) [])).comp (ListReverse.loop ea a0)).congr _
    (fun _ => List.append_nil _)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryListFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace ListFold
variable {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (a0 : α)
variable (op : β × α → β)

noncomputable def program (P : PolyProgram (encodePair eb ea) eb op) :
    PolyProgram (enc ea eb) (encodeLoop (enc ea eb) eb) (body a0 op) := by
  let px := PolyProgram.fst (encodeList ea) eb
  let py := PolyProgram.snd (encodeList ea) eb
  let hd := px.comp (PolyProgram.listHead ea a0)
  let tl := px.comp (PolyProgram.listTail ea a0)
  let newLast := (py.fanout hd).comp P
  let recur := (tl.fanout newLast).comp (PolyProgram.injectRight (enc ea eb) eb)
  let done := py.comp (PolyProgram.injectLeft (enc ea eb) eb)
  exact (PolyProgram.ite (px.comp (PolyProgram.listIsEmpty ea)) recur done).congr _ (fun _ => rfl)

noncomputable def loop (P : PolyProgram (encodePair eb ea) eb op) (B : Polynomial ℕ)
    (hB : ∀ (as : List α) (b : β) pre suf, as=pre++suf →
      (eb (pre.foldl (fun b a => op (b,a)) b)).length ≤ B.eval (enc ea eb (as,b)).length) :
    PolyProgram (enc ea eb) eb (result op) :=
  (program ea eb a0 op P).loop (result op) (X+1) (2*X+1+B) (fun s => by
    refine ⟨s.1.length+1,?_,?_⟩
    · have h := EncodedList.length_le ea s.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]; omega
    · apply run
      intro pre suf he
      have hh := hB s.1 s.2 pre suf he
      have hx : (encodeList ea suf).length ≤ (encodeList ea s.1).length := by
        rw [he,EncodedList.append,List.length_append]
        omega
      simp only [enc,encodePair_length] at hh ⊢
      simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
      omega)

end ListFold

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {op : β × α → β}
noncomputable def listFold (P : PolyProgram (encodePair eb ea) eb op) (a0 : α) (B : Polynomial ℕ)
    (hB : ∀ (as : List α) (b : β) pre suf, as=pre++suf →
      (eb (pre.foldl (fun b a => op (b,a)) b)).length ≤ B.eval (encodePair (encodeList ea) eb (as,b)).length) :
    PolyProgram (encodePair (encodeList ea) eb) eb (fun x => x.1.foldl (fun b a => op (b,a)) x.2) :=
  ListFold.loop ea eb a0 op P B hB
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryNatural
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace PolyProgram
noncomputable def natBit : PolyProgram (encodePair encodeBool Nat.bits) Nat.bits (fun x : Bool × ℕ => Nat.bit x.1 x.2) :=
  (cons.comp toBits).recode (fun x => (x.1,x.2.bits)) (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,Word.value_cons,Word.value_bits,Nat.bit_val,Nat.add_comm])

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryListContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
noncomputable def listMapWith {f : γ × α → β}
    (P : PolyProgram (encodePair ec ea) eb f) (a0 : α) (b0 : β) :
    PolyProgram (encodePair ec (encodeList ea)) (encodeList eb) (fun x => x.2.map (fun a => f (x.1,a))) := by
  let eacc := encodePair ec (encodeList eb)
  let acc := fst eacc ea
  let c := acc.comp (fst ec (encodeList eb))
  let bs := acc.comp (snd ec (encodeList eb))
  let a := snd eacc ea
  let nb := ((c.fanout a).comp P).fanout bs
  let step : PolyProgram (encodePair eacc ea) eacc (fun x : (γ × List β) × α => (x.1.1,f (x.1.1,x.2)::x.1.2)) :=
    (c.fanout (nb.comp (listCons eb))).congr _ (fun _ => rfl)
  let B : Polynomial ℕ := 3*X+X*(2*P.sizeBound.comp (3*X+1)+1)+1
  let fold := step.listFold a0 B (by
    intro as x pre suf he
    let L := (encodePair (encodeList ea) eacc (as,x)).length
    have hc : (ec x.1).length ≤ L := by simp only [L,eacc,encodePair_length]; omega
    have hb : (encodeList eb x.2).length ≤ L := by simp only [L,eacc,encodePair_length]; omega
    have hp : (encodeList ea pre).length ≤ L := by
      have hh : (encodeList ea pre).length ≤ (encodeList ea as).length := by rw [he,EncodedList.append,List.length_append]; omega
      simp only [L,encodePair_length]; omega
    have hplen : pre.length ≤ L := (EncodedList.length_le ea pre).trans hp
    have hout := EncodedList.length_bound eb (pre.map (fun a => f (x.1,a))) (P.sizeBound.eval (3*L+1)) (by
      intro b hb
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
      apply (P.length_bound (x.1,a)).trans
      apply polynomial_eval_mono
      have hla := (EncodedList.member_length ea pre a ha).trans hp
      simp only [encodePair_length]
      omega)
    rw [List.length_map] at hout
    simp only [ListAlgorithms.pushMapWith_pair,eacc,encodePair_length,EncodedList.append,List.length_append,EncodedList.reverse_length]
    simp only [B,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,eval_comp]
    simp only [L,eacc,encodePair_length] at hc hb hplen hout
    nlinarith)
  let start := (snd ec (encodeList ea)).fanout ((fst ec (encodeList ea)).fanout (constant (encodePair ec (encodeList ea)) (encodeList eb) []))
  exact (((start.comp fold).comp (snd ec (encodeList eb))).comp (listReverse eb b0)).congr _ (fun x => by
    simp only [Function.comp_apply,ListAlgorithms.pushMapWith,List.append_nil,List.reverse_reverse])

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinarySubtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace SubtractionLoop
open AdditionLoop (S ec ey enc enc_length)

noncomputable def program : PolyProgram enc (encodeLoop enc ec) body := by
  let px := PolyProgram.fst id ey
  let pyz := PolyProgram.snd id ey
  let py := pyz.comp (PolyProgram.fst id ec)
  let pca := pyz.comp (PolyProgram.snd id ec)
  let pc := pca.comp (PolyProgram.fst encodeBool id)
  let pa := pca.comp (PolyProgram.snd encodeBool id)
  let bits := (px.comp PolyProgram.head).fanout ((py.comp PolyProgram.head).fanout pc)
  let binj := encodePair_injective encodeBool_injective (encodePair_injective encodeBool_injective encodeBool_injective)
  let sb := bits.comp (PolyProgram.boolFunction _ encodeBool (fun v : Bool × (Bool × Bool) => Word.sumBit v.1 v.2.1 v.2.2) binj)
  let cb := bits.comp (PolyProgram.boolFunction _ encodeBool (fun v : Bool × (Bool × Bool) => Word.borrowBit v.1 v.2.1 v.2.2) binj)
  let na := (sb.fanout pa).comp PolyProgram.cons
  let pn := (px.comp PolyProgram.tail).fanout ((py.comp PolyProgram.tail).fanout (cb.fanout na))
  let pe := ((px.comp PolyProgram.isEmpty).fanout (py.comp PolyProgram.isEmpty)).comp PolyProgram.boolAnd
  let pf := pc.fanout (pa.comp PolyProgram.reverse)
  exact (PolyProgram.ite pe (pn.comp (PolyProgram.injectRight enc ec))
    (pf.comp (PolyProgram.injectLeft enc ec))).congr _ (fun _ => rfl)

noncomputable def loop : PolyProgram enc ec result :=
  program.loop result (X+1) X (fun s => by
    obtain ⟨n,hn,hr⟩ := run (s.1.length+s.2.1.length) s (enc s).length rfl le_rfl
    refine ⟨n,?_,?_⟩
    · simp only [eval_add,eval_X,eval_one,enc_length]; omega
    · simpa only [eval_X] using hr)
end SubtractionLoop

namespace PolyProgram
noncomputable def subWords : PolyProgram (encodePair id id) AdditionLoop.ec (fun x : List Bool × List Bool => Word.sub x.1 x.2 false) := by
  let ex : List Bool × List Bool → List Bool := encodePair id id
  let init := (fst id id).fanout ((snd id id).fanout (constant ex AdditionLoop.ec (false,[])))
  exact (init.comp SubtractionLoop.loop).congr _ (fun _ => rfl)

noncomputable def natLT : PolyProgram (encodePair Nat.bits Nat.bits) encodeBool (fun x : ℕ × ℕ => decide (x.1<x.2)) :=
  (subWords.comp (fst encodeBool id)).recode (fun x => (x.1.bits,x.2.bits)) (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,Word.sub_borrow,Word.value_bits])

noncomputable def natSub : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1-x.2) := by
  let clamp := ite (fst encodeBool id) (snd encodeBool id) (constant AdditionLoop.ec id [])
  exact ((subWords.comp clamp).comp toBits).recode (fun x => (x.1.bits,x.2.bits)) (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,Word.sub_clamp,Word.value_bits])
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryMultiplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace MultiplicationLoop

noncomputable def program : PolyProgram enc (encodeLoop enc Nat.bits) body := by
  let px := PolyProgram.fst Nat.bits ey
  let pyz := PolyProgram.snd Nat.bits ey
  let py := pyz.comp (PolyProgram.fst Nat.bits Nat.bits)
  let pa := pyz.comp (PolyProgram.snd Nat.bits Nat.bits)
  let half := px.comp PolyProgram.natHalf
  let twice := ((PolyProgram.constant enc encodeBool false).fanout py).comp PolyProgram.natBit
  let acc := PolyProgram.ite (px.comp PolyProgram.natOdd) pa ((pa.fanout py).comp PolyProgram.natAdd)
  let pn := half.fanout (twice.fanout acc)
  exact (PolyProgram.ite (px.comp PolyProgram.natZero)
    (pn.comp (PolyProgram.injectRight enc Nat.bits))
    (pa.comp (PolyProgram.injectLeft enc Nat.bits))).congr _ (fun s => by
      simp only [Function.comp_apply,body,decide_eq_true_eq]
      rfl)

 theorem run (L : ℕ) : ∀ (s : S) (S : ℕ), s.1.bits.length=L → 3*potential s+2≤S →
    ∃ n≤L+1, BoundedRun enc body S n s (result s) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
      intro s S hL hs
      have hsize := (length_le_potential s).trans hs
      by_cases hz : s.1=0
      · refine ⟨1,by omega,BoundedRun.stop hsize ?_⟩
        simp only [body,hz,ite_true,result,zero_mul,zero_add]
      · have hl : (next s).1.bits.length<L := by simpa only [next,hL] using NatBinary.half_lt_length hz
        have hb : 3*potential (next s)+2≤S := by have := next_potential s hz; omega
        obtain ⟨n,hn,hr⟩ := ih _ hl (next s) S rfl hb
        refine ⟨n+1,by omega,?_⟩
        rw [next_result] at hr
        exact BoundedRun.step hsize (by simp only [body,hz,ite_false]) hr

end MultiplicationLoop

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryInteger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace PolyProgram

noncomputable def intFromParts : PolyProgram signedParts Signed.encode (fun x => Signed.value x.1 x.2) := by
  let ps := fst encodeBool Nat.bits
  let pn := snd encodeBool Nat.bits
  let s := (ps.fanout ((pn.comp natZero).comp boolNot)).comp boolAnd
  exact (s.fanout pn).recode id (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,id_eq,Signed.encode,Signed.parts,Signed.sign_value,Signed.abs_value])

noncomputable def intOfNat : PolyProgram Nat.bits Signed.encode Nat.cast :=
  (((constant Nat.bits encodeBool false).fanout (identity Nat.bits)).comp intFromParts).congr _ (fun _ => rfl)

noncomputable def intAdd : PolyProgram (encodePair Signed.encode Signed.encode) Signed.encode (fun x : ℤ × ℤ => x.1+x.2) := by
  let px := fst Signed.encode Signed.encode
  let py := snd Signed.encode Signed.encode
  let sx := px.comp intSign
  let sy := py.comp intSign
  let nx := px.comp intAbs
  let ny := py.comp intAbs
  let plus := ((sx.fanout ((nx.fanout ny).comp natAdd)).comp intFromParts)
  let minusX := (sx.fanout ((nx.fanout ny).comp natSub)).comp intFromParts
  let minusY := (sy.fanout ((ny.fanout nx).comp natSub)).comp intFromParts
  let minus := ite ((nx.fanout ny).comp natLT) minusX minusY
  refine (ite ((sx.fanout sy).comp boolEq) minus plus).congr _ ?_
  intro x
  simpa only [Function.comp_apply, decide_eq_true_eq, Signed.add, Signed.value_parts]
    using Signed.value_add (Signed.sign x.1) (Signed.sign x.2) x.1.natAbs x.2.natAbs

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryAutomatic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Binary.Automatic
open PolyProgram Function
instance instCodingInt : Coding ℤ := ⟨Signed.encode⟩

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]
@[fun_prop] theorem const (b : β) : Poly (fun _ : α => b) := ⟨PolyProgram.constant enc enc b⟩
@[fun_prop] theorem comp {f : β → γ} {g : α → β} (hf : Poly f) (hg : Poly g) : Poly (fun a => f (g a)) :=
  ⟨hg.program.comp hf.program⟩
@[fun_prop] theorem pair {f : α → β} {g : α → γ} (hf : Poly f) (hg : Poly g) : Poly (fun a => (f a,g a)) :=
  ⟨hf.program.fanout hg.program⟩
@[fun_prop] theorem fst : Poly (Prod.fst : α × β → α) := ⟨PolyProgram.fst enc enc⟩
@[fun_prop] theorem snd : Poly (Prod.snd : α × β → β) := ⟨PolyProgram.snd enc enc⟩
@[fun_prop] theorem ite {p : α → Bool} {f g : α → β} (hp : Poly p) (hf : Poly f) (hg : Poly g) :
    Poly (fun x => if p x then f x else g x) := ⟨(PolyProgram.ite hp.program hg.program hf.program).congr _ (fun _ => rfl)⟩

@[fun_prop] theorem list_map [Inhabited β] [Inhabited γ] {f : α → β → γ} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).map (f x)) :=
  ⟨((PolyProgram.identity enc).fanout ha.program).comp (hf.program.listMapWith default default)⟩

end Poly
end MetricKMedian.Binary.Automatic
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_GraphListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseGraph.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly
abbrev er := encodeList encodeBool
end MetricKMedian.SparseGraph.ListOperation
end

end OAI
end


