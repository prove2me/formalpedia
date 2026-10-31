-- Prove2me | Definitions.Def_OAIQ053K013
-- name    : OAIQ053K013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:54:57.499992+00:00
-- url     : https://prove2.me/theorems/84c21b1f-31b2-483b-8594-2c8db1242c1c
-- title:
--   Definitions bundle OAIQ053K013 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 152 declarations of OpenAI's Lean: 80 definitions and 72 theorems. The definitions and types are `OAI.MetricKMedian.Binary.Loop.Key`, `OAI.MetricKMedian.Binary.Loop.Label`, `OAI.MetricKMedian.Binary.Loop.State`, `OAI.MetricKMedian.Binary.Loop.auxiliary`, `OAI.MetricKMedian.Binary.Loop.body`, `OAI.MetricKMedian.Binary.Loop.check`, `OAI.MetricKMedian.Binary.Loop.checkCfg`, `OAI.MetricKMedian.Binary.Loop.checkCode`, `OAI.MetricKMedian.Binary.Loop.clean`, `OAI.MetricKMedian.Binary.Loop.code`, `OAI.MetricKMedian.Binary.Loop.following`, `OAI.MetricKMedian.Binary.Loop.machine`, `OAI.MetricKMedian.Binary.Loop.phase`, `OAI.MetricKMedian.Binary.Loop.source`, `OAI.MetricKMedian.Binary.Loop.target`, `OAI.MetricKMedian.Binary.Loop.transfer`, `OAI.MetricKMedian.Binary.Loop.transferCfg`, `OAI.MetricKMedian.Binary.ParallelTransducer.code`, `OAI.MetricKMedian.Binary.ParallelTransducer.emit`, `OAI.MetricKMedian.Binary.ParallelTransducer.emitPair`, `OAI.MetricKMedian.Binary.ParallelTransducer.input`, `OAI.MetricKMedian.Binary.ParallelTransducer.leftCfg`, `OAI.MetricKMedian.Binary.ParallelTransducer.machine`, `OAI.MetricKMedian.Binary.ParallelTransducer.output`, `OAI.MetricKMedian.Binary.ParallelTransducer.program`, `OAI.MetricKMedian.Binary.ParallelTransducer.readCfg`, `OAI.MetricKMedian.Binary.ParallelTransducer.right`, `OAI.MetricKMedian.Binary.ParallelTransducer.rightCfg`, `OAI.MetricKMedian.Binary.ParallelTransducer.store`, `OAI.MetricKMedian.Binary.ParallelTransducer.transfer`, `OAI.MetricKMedian.Binary.PolyProgram.comp`, `OAI.MetricKMedian.Binary.PolyProgram.congr`, `OAI.MetricKMedian.Binary.PolyProgram.cons`, `OAI.MetricKMedian.Binary.PolyProgram.constant`, `OAI.MetricKMedian.Binary.PolyProgram.duplicate`, `OAI.MetricKMedian.Binary.PolyProgram.exchange`, `OAI.MetricKMedian.Binary.PolyProgram.fanout`, `OAI.MetricKMedian.Binary.PolyProgram.fst`, `OAI.MetricKMedian.Binary.PolyProgram.head`, `OAI.MetricKMedian.Binary.PolyProgram.identity` and 40 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedian_Binary_BooleanEncoding`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Binary/BooleanEncoding.lean), [`KMedian_Binary_BooleanListPrimitives`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Binary/BooleanListPrimitives.lean), [`KMedian_Binary_BooleanLoop`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Binary/BooleanLoop.lean), [`KMedian_Binary_BooleanMachine`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Binary/BooleanMachine.lean), [`KMedian_Binary_BooleanParallelTransducer`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Binary/BooleanParallelTransducer.lean), [`KMedian_Binary_BooleanPolynomial`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Binary/BooleanPolynomial.lean), [`KMedian_Binary_BooleanProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Binary/BooleanProducts.lean), [`KMedian_Binary_BooleanReverse`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Binary/BooleanReverse.lean), [`KMedian_Binary_BooleanThread`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Binary/BooleanThread.lean).
--
--   **Imports.** It imports the bundles `OAIQ053K000` and `OAIQ053K001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K028`, `OAIQ053K029` and `OAIQ053K033`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K000
import Definitions.Def_OAIQ053K001

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BooleanMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Turing StateTransition Function Finset

attribute [instance] Machine.decK Machine.finK Machine.finLabel Machine.finState

namespace Trace
variable {α β : Type*} {f : α → Option α}

theorem of_iterate {n : ℕ} {a b : α}
    (h : (flip bind f)^[n] (some a)=some b) : Trace f n a b := by
  induction n generalizing a with
  | zero =>
      have hab : a=b := Option.some.inj h
      subst b
      exact refl a
  | succ n ih =>
      rw [Function.iterate_succ_apply] at h
      cases hc : f a with
      | none =>
          have hz : ∀ t : ℕ, (flip bind f)^[t] (none : Option α)=none := by
            intro t
            induction t with
            | zero => rfl
            | succ t iht =>
                rw [Function.iterate_succ_apply]
                exact iht
          change (flip bind f)^[n] (f a)=some b at h
          rw [hc,hz] at h
          contradiction
      | some c =>
          have hh : (flip bind f)^[n] (some c)=some b := by
            change (flip bind f)^[n] (f a)=some b at h
            rwa [hc] at h
          exact cons hc (ih hh)

end Trace

namespace Machine
variable {K L S : Type} [DecidableEq K]

variable [Fintype K]

theorem stepAux_volume (q : TM2.Stmt (fun _ : K => Bool) L S)
    (v : S) (s : K → List Bool) :
    volume (TM2.stepAux q v s).stk ≤ volume s+pushes q := by
  induction q generalizing v s with
  | push k g q ih =>
      have h := ih v (update s k (g v::s k))
      have hv := volume_update s k (g v::s k)
      simp only [List.length_cons] at hv
      simpa only [TM2.stepAux,pushes,Nat.add_assoc] using (by omega :
        volume (TM2.stepAux q v (update s k (g v::s k))).stk≤volume s+(1+pushes q))
  | peek k g q ih => exact ih _ _
  | pop k g q ih =>
      have h := ih (g v (s k).head?) (update s k (s k).tail)
      have hv := volume_update s k (s k).tail
      have hl := List.length_tail (l := s k)
      simp only [TM2.stepAux,pushes]
      omega
  | load g q ih => exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v
      · simpa only [TM2.stepAux,hg,Bool.false_eq_true,Bool.cond_false,pushes] using
          (ihr v s).trans (Nat.add_le_add_left (le_max_right (pushes q) _) _)
      · simpa only [TM2.stepAux,hg,Bool.cond_true,pushes] using
          (ihq v s).trans (Nat.add_le_add_left (le_max_left _ (pushes r)) _)
  | goto g => simp only [TM2.stepAux,pushes,Nat.add_zero,le_refl]
  | halt => simp only [TM2.stepAux,pushes,Nat.add_zero,le_refl]

theorem step_volume (M : Machine) (a b : M.Cfg) (h : M.step a=some b) :
    volume b.stk ≤ volume a.stk+M.growth := by
  rcases a with ⟨l,v,s⟩
  cases l with
  | none => cases h
  | some l =>
      have hb : b=TM2.stepAux (M.code l) v s := (Option.some.inj h).symm
      rw [hb]
      exact (stepAux_volume _ _ _).trans (Nat.add_le_add_left
        (show pushes (M.code l) ≤ M.growth from
          single_le_sum (f:=fun x => pushes (M.code x)) (fun _ _ => Nat.zero_le _) (mem_univ l)) _)

theorem trace_volume (M : Machine) {n : ℕ} {a b : M.Cfg}
    (h : Trace M.step n a b) : volume b.stk ≤ volume a.stk+n*M.growth := by
  induction h with
  | refl => simp
  | @cons n a b c hab hbc ih =>
      have hs := M.step_volume a b hab
      calc
        _ ≤ volume b.stk+n*M.growth := ih
        _ ≤ volume a.stk+(n+1)*M.growth := by rw [Nat.add_mul]; omega

theorem output_length (M : Machine) {s t : List Bool} {n : ℕ}
    (h : TM2OutputsInTime M.tm s (some t) n) : t.length ≤ s.length+n*M.growth := by
  have ht : Trace M.step h.steps (M.initialCfg s) (M.finalCfg t) :=
    Trace.of_iterate h.evals_in_steps
  have hv := M.trace_volume ht
  simp only [initial_volume,final_volume] at hv
  exact hv.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ h.steps_le_m) _)

end Machine
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BooleanPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Turing Polynomial

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
variable {f : α → β} {g : β → γ}

 theorem length_bound (P : PolyProgram ea eb f) (a : α) :
    (eb (f a)).length ≤ P.sizeBound.eval (ea a).length := by
  simpa only [sizeBound,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    using P.machine.output_length (P.outputs a)

 noncomputable def comp (P : PolyProgram ea eb f) (Q : PolyProgram eb ec g) : PolyProgram ea ec (g ∘ f) where
  machine := Compose.machine P.machine Q.machine
  time := P.compTime Q
  outputs a := by
    let hP := P.outputs a
    let hQ := Q.outputs (f a)
    have tP : Trace P.machine.step hP.steps (P.machine.initialCfg (ea a))
        (P.machine.finalCfg (eb (f a))) := Trace.of_iterate hP.evals_in_steps
    have tQ : Trace Q.machine.step hQ.steps (Q.machine.initialCfg (eb (f a)))
        (Q.machine.finalCfg (ec (g (f a)))) := Trace.of_iterate hQ.evals_in_steps
    have h := Compose.run P.machine Q.machine tP tQ
    refine ⟨⟨_,h.iterate_eq⟩,?_⟩
    have hl := P.length_bound a
    have hqp := (hQ.steps_le_m).trans (polynomial_eval_mono Q.time hl)
    have hpp := hP.steps_le_m
    simp only [compTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_comp]
    omega

 def congr (P : PolyProgram ea eb f) (f' : α → β) (h : ∀ a, f a=f' a) : PolyProgram ea eb f' where
  machine := P.machine
  time := P.time
  outputs a := by rw [← h a]; exact P.outputs a

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BooleanEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace PolyProgram

 noncomputable def fst {α β : Type} (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram (encodePair ea eb) ea Prod.fst :=
  (WordTransducer.projecting false).program.of_word (fun _ => by
    simpa only [encodePair,Bool.false_eq_true,ite_false,WordTransducer.projecting] using WordTransducer.projecting_pair false _ _)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BooleanLoop
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
abbrev Key := M.K ⊕ Unit
abbrev Label := M.Label ⊕ Option Bool
abbrev State := M.State × Option Bool
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

end Loop

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
variable {f : α → β ⊕ α}

noncomputable def passTime (P : PolyProgram ea (encodeLoop ea eb) f) (S : ℕ) : ℕ :=
  P.time.eval S+2*P.sizeBound.eval S+3

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BooleanParallelTransducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section
namespace MetricKMedian.Binary
open Turing Function Polynomial Finset

attribute [instance] ParallelTransducer.finiteQ

namespace ParallelTransducer
variable (T : ParallelTransducer)

abbrev input : Key := 0
abbrev right : Key := 2
abbrev output : Key := 3

def store (xs ls rs ys : List Bool) : Key → List Bool :=
  fun k => if k=input then xs else if k=left then ls else if k=right then rs else ys

 theorem store_update_input (xs ls rs ys zs : List Bool) :
    update (store xs ls rs ys) input zs=store zs ls rs ys := by
  funext k
  fin_cases k <;> simp [store,input,left,right]
 theorem store_update_left (xs ls rs ys zs : List Bool) :
    update (store xs ls rs ys) left zs=store xs zs rs ys := by
  funext k
  fin_cases k <;> simp [store,input,left,right]
 theorem store_update_right (xs ls rs ys zs : List Bool) :
    update (store xs ls rs ys) right zs=store xs ls zs ys := by
  funext k
  fin_cases k <;> simp [store,input,left,right]
 theorem store_update_output (xs ls rs ys zs : List Bool) :
    update (store xs ls rs ys) output zs=store xs ls rs zs := by
  funext k
  fin_cases k <;> simp [store,input,left,right,output]

def emit (k : Key) : List Bool → TM2.Stmt (fun _ : Key => Bool) (Label T) State →
    TM2.Stmt (fun _ : Key => Bool) (Label T) State
  | [], s => s
  | b::bs, s => .push k (fun _ => b) (emit k bs s)

 theorem emit_step (k : Key) (bits : List Bool) (s : TM2.Stmt (fun _ : Key => Bool) (Label T) State)
    (v : State) (stk : Key → List Bool) :
    TM2.stepAux (emit T k bits s) v stk=TM2.stepAux s v (update stk k (bits.reverse++stk k)) := by
  induction bits generalizing stk with
  | nil => simp only [emit,List.reverse_nil,List.nil_append,update_eq_self]
  | cons b bs ih =>
      simp only [emit,TM2.stepAux,ih,update_self,update_idem,List.reverse_cons,
        List.append_assoc,List.singleton_append]

def emitPair (p : List Bool × List Bool) (s : TM2.Stmt (fun _ : Key => Bool) (Label T) State) :=
  emit T left p.1 (emit T right p.2 s)

 theorem emitPair_step (p : List Bool × List Bool) (s : TM2.Stmt (fun _ : Key => Bool) (Label T) State)
    (v : State) (xs ls rs ys : List Bool) :
    TM2.stepAux (emitPair T p s) v (store xs ls rs ys)=
      TM2.stepAux s v (store xs (p.1.reverse++ls) (p.2.reverse++rs) ys) := by
  simp [emitPair,emit_step,store,input,left,right,store_update_left,store_update_right]

def transfer (phase : Bool) : TM2.Stmt (fun _ : Key => Bool) (Label T) State :=
  .pop (if phase then left else right) (fun _ b => b)
    (.branch Option.isSome
      (.push output (fun b => b.getD false) (.load (fun _ => none) (.goto (fun _ => .inr phase))))
      (.load (fun _ => none) (if phase then .halt else .goto (fun _ => .inr true))))

def code : Label T → TM2.Stmt (fun _ : Key => Bool) (Label T) State
  | .inl q => .pop input (fun _ b => b)
      (.branch Option.isSome
        (.branch (fun b => b.getD false)
          (.load (fun _ => none) (emitPair T (T.next q true).2 (.goto (fun _ => .inl (T.next q true).1))))
          (.load (fun _ => none) (emitPair T (T.next q false).2 (.goto (fun _ => .inl (T.next q false).1)))))
        (.load (fun _ => none) (emitPair T (T.finish q) (.goto (fun _ => .inr false)))))
  | .inr b => transfer T b

abbrev machine : Machine where
  K := Key
  input := input
  output := output
  Label := Label T
  main := .inl T.initial
  State := State
  initial := none
  code := code T

def readCfg (q : T.Q) (xs ls rs : List Bool) : (machine T).Cfg :=
  ⟨some (.inl q),none,store xs ls rs []⟩
def rightCfg (ls rs ys : List Bool) : (machine T).Cfg :=
  ⟨some (.inr false),none,store [] ls rs ys⟩
def leftCfg (ls ys : List Bool) : (machine T).Cfg :=
  ⟨some (.inr true),none,store [] ls [] ys⟩

 theorem read_cons (q : T.Q) (b : Bool) (xs ls rs : List Bool) :
    (machine T).step (T.readCfg q (b::xs) ls rs)=
      some (T.readCfg (T.next q b).1 xs ((T.next q b).2.1.reverse++ls) ((T.next q b).2.2.reverse++rs)) := by
  cases b <;> simp [readCfg,TM2.step,code,TM2.stepAux,store,input,emitPair_step,store_update_input]

 theorem read_nil (q : T.Q) (ls rs : List Bool) :
    (machine T).step (T.readCfg q [] ls rs)=
      some (T.rightCfg ((T.finish q).1.reverse++ls) ((T.finish q).2.reverse++rs) []) := by
  simp [readCfg,rightCfg,TM2.step,code,TM2.stepAux,store,input,emitPair_step,store_update_input]

 theorem read_run (q : T.Q) (xs ls rs : List Bool) :
    Trace (machine T).step (xs.length+1) (T.readCfg q xs ls rs)
      (T.rightCfg ((T.run q xs).1.reverse++ls) ((T.run q xs).2.reverse++rs) []) := by
  induction xs generalizing q ls rs with
  | nil => exact Trace.cons (T.read_nil q ls rs) (Trace.refl _)
  | cons b xs ih =>
      simpa only [run,List.length_cons,List.reverse_append,List.append_assoc] using
        Trace.cons (T.read_cons q b xs ls rs)
          (ih (T.next q b).1 ((T.next q b).2.1.reverse++ls) ((T.next q b).2.2.reverse++rs))

 theorem right_cons (b : Bool) (ls rs ys : List Bool) :
    (machine T).step (T.rightCfg ls (b::rs) ys)=some (T.rightCfg ls rs (b::ys)) := by
  simp [rightCfg,TM2.step,code,transfer,TM2.stepAux,store,input,left,right,output,store_update_right,store_update_output]

 theorem right_nil (ls ys : List Bool) :
    (machine T).step (T.rightCfg ls [] ys)=some (T.leftCfg ls ys) := by
  simp [rightCfg,leftCfg,TM2.step,code,transfer,TM2.stepAux,store,input,left,right,output,store_update_right]

 theorem right_run (ls rs ys : List Bool) :
    Trace (machine T).step (rs.length+1) (T.rightCfg ls rs ys) (T.leftCfg ls (rs.reverse++ys)) := by
  induction rs generalizing ys with
  | nil => exact Trace.cons (T.right_nil ls ys) (Trace.refl _)
  | cons b rs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (T.right_cons b ls rs ys) (ih (b::ys))

 theorem left_cons (b : Bool) (ls ys : List Bool) :
    (machine T).step (T.leftCfg (b::ls) ys)=some (T.leftCfg ls (b::ys)) := by
  simp [leftCfg,TM2.step,code,transfer,TM2.stepAux,store,input,left,right,output,store_update_left,store_update_output]

 theorem left_nil (ys : List Bool) :
    (machine T).step (T.leftCfg [] ys)=some ((machine T).finalCfg ys) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    fin_cases k <;> simp [Machine.finalCfg,code,transfer,TM2.stepAux,store,input,left,right,output]

 theorem left_run (ls ys : List Bool) :
    Trace (machine T).step (ls.length+1) (T.leftCfg ls ys) ((machine T).finalCfg (ls.reverse++ys)) := by
  induction ls generalizing ys with
  | nil => exact Trace.cons (T.left_nil ys) (Trace.refl _)
  | cons b ls ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (T.left_cons b ls ys) (ih (b::ys))

 theorem run_trace (xs : List Bool) :
    Trace (machine T).step (xs.length+(T.run T.initial xs).1.length+(T.run T.initial xs).2.length+3)
      ((machine T).initialCfg xs)
      ((machine T).finalCfg ((T.run T.initial xs).1++(T.run T.initial xs).2)) := by
  have hi : (machine T).initialCfg xs=T.readCfg T.initial xs [] [] := by
    apply cfg_ext <;> try rfl
    funext k
    fin_cases k <;> simp [Machine.initialCfg,readCfg,store,input,left,right]
  rw [hi]
  have hr := T.read_run T.initial xs [] []
  simp only [List.append_nil] at hr
  have hs := T.right_run (T.run T.initial xs).1.reverse (T.run T.initial xs).2.reverse []
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hs
  have ht := T.left_run (T.run T.initial xs).1.reverse (T.run T.initial xs).2
  simp only [List.length_reverse,List.reverse_reverse] at ht
  have h := (hr.trans hs).trans ht
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  omega

noncomputable def program : PolyProgram id id (fun xs => (T.run T.initial xs).1++(T.run T.initial xs).2) where
  machine := machine T
  time := C (T.width+1)*X+C (T.width+3)
  outputs xs := by
    refine ⟨⟨_,(T.run_trace xs).iterate_eq⟩,?_⟩
    have hl := T.run_length T.initial xs
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,id_eq]
    nlinarith

end ParallelTransducer
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BooleanThread
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace Thread
variable (M : Machine)
abbrev Key := M.K ⊕ Bool
abbrev Label := M.Label ⊕ Fin 4
abbrev State := M.State × Option Bool
abbrev source : Key M := .inr false
abbrev buffer : Key M := .inr true
abbrev reading : Label M := .inr 0
abbrev loading : Label M := .inr 1
abbrev emitting : Label M := .inr 2
abbrev draining : Label M := .inr 3

def store (s : M.K → List Bool) (xs ys : List Bool) : Key M → List Bool :=
  fun k => match k with
  | .inl k => s k
  | .inr false => xs
  | .inr true => ys

@[simp] theorem store_local (s : M.K → List Bool) (xs ys : List Bool) (k : M.K) :
    store M s xs ys (.inl k)=s k := rfl
@[simp] theorem store_source (s : M.K → List Bool) (xs ys : List Bool) :
    store M s xs ys (source M)=xs := rfl
@[simp] theorem store_buffer (s : M.K → List Bool) (xs ys : List Bool) :
    store M s xs ys (buffer M)=ys := rfl

def slot (k : M.K) (xs : List Bool) : M.K → List Bool := fun j => if j=k then xs else []

 theorem slot_nil (k : M.K) : slot M k []=fun _ => [] := by funext j; simp [slot]
 theorem slot_self (k : M.K) (xs : List Bool) : slot M k xs k=xs := by simp [slot]
 theorem slot_update (k : M.K) (xs ys : List Bool) : update (slot M k xs) k ys=slot M k ys := by
  funext j
  by_cases h : j=k <;> simp [slot,h]

 theorem store_update_local (s : M.K → List Bool) (xs ys : List Bool) (k : M.K) (w : List Bool) :
    update (store M s xs ys) (.inl k) w=store M (update s k w) xs ys := by
  funext j
  rcases j with j | j
  · simp [store,update_apply]
  · cases j <;> simp [store]
 theorem store_update_source (s : M.K → List Bool) (xs ys w : List Bool) :
    update (store M s xs ys) (source M) w=store M s w ys := by
  funext j
  rcases j with j | j <;> try cases j
  all_goals simp [store]
 theorem store_update_buffer (s : M.K → List Bool) (xs ys w : List Bool) :
    update (store M s xs ys) (buffer M) w=store M s xs w := by
  funext j
  rcases j with j | j <;> try cases j
  all_goals simp [store]

def body (tail : List Bool) : Embedding M.K M.Label M.State (Key M) (Label M) (State M) where
  key := Sum.inl
  read := Prod.fst
  write v x := (x,v.2)
  state v := (v,none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := store M s tail []
  stack_key _ _ := rfl
  stack_update s k x := (store_update_local M s tail [] k x).symm
  label := Sum.inl
  halted := some (emitting M)
  stop := .goto (fun _ => emitting M)
  stop_spec _ _ := rfl

 theorem body_stmt (tail : List Bool) (s : TM2.Stmt (fun _ : M.K => Bool) M.Label M.State) :
    (body M tail).stmt s=(body M []).stmt s := by
  induction s <;> simp_all [Embedding.stmt,body]

def clean (v : State M) : State M := (v.1,none)

def readCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (source M) (fun v b => (v.1,b))
    (.branch (fun v => v.2.getD false)
      (.pop (source M) (fun v b => (v.1,b))
        (.push (buffer M) (fun v => v.2.getD false)
          (.load (clean M) (.goto (fun _ => reading M)))))
      (.load (clean M) (.goto (fun _ => loading M))))

def loadCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (buffer M) (fun v b => (v.1,b))
    (.branch (fun v => v.2.isSome)
      (.push (.inl M.input) (fun v => v.2.getD false)
        (.load (clean M) (.goto (fun _ => loading M))))
      (.load (clean M) (.goto (fun _ => .inl M.main))))

def emitCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (.inl M.output) (fun v b => (v.1,b))
    (.branch (fun v => v.2.isSome)
      (.push (buffer M) (fun _ => true) (.push (buffer M) (fun v => v.2.getD false)
        (.load (clean M) (.goto (fun _ => emitting M)))))
      (.push (buffer M) (fun _ => false)
        (.load (clean M) (.goto (fun _ => draining M)))))

def drainCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (buffer M) (fun v b => (v.1,b))
    (.branch (fun v => v.2.isSome)
      (.push (source M) (fun v => v.2.getD false)
        (.load (clean M) (.goto (fun _ => draining M))))
      (.load (clean M) .halt))

def code : Label M → TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M)
  | .inl l => (body M []).stmt (M.code l)
  | .inr i => if i=0 then readCode M else if i=1 then loadCode M else if i=2 then emitCode M else drainCode M

abbrev machine : Machine where
  K := Key M
  input := source M
  output := source M
  Label := Label M
  main := reading M
  State := State M
  initial := (M.initial,none)
  code := code M

 theorem code_body (tail : List Bool) (l : M.Label) :
    (machine M).code ((body M tail).label l)=(body M tail).stmt (M.code l) := (body_stmt M tail _).symm

def readCfg (xs tail buf : List Bool) : (machine M).Cfg :=
  ⟨some (reading M),(M.initial,none),store M (fun _ => []) (quote xs++tail) buf⟩

def loadCfg (tail buf xs : List Bool) : (machine M).Cfg :=
  ⟨some (loading M),(M.initial,none),store M (slot M M.input xs) tail buf⟩

def emitCfg (tail xs buf : List Bool) : (machine M).Cfg :=
  ⟨some (emitting M),(M.initial,none),store M (slot M M.output xs) tail buf⟩

def drainCfg (tail buf : List Bool) : (machine M).Cfg :=
  ⟨some (draining M),(M.initial,none),store M (fun _ => []) tail buf⟩

 theorem read_cons (b : Bool) (xs tail buf : List Bool) :
    (machine M).step (readCfg M (b::xs) tail buf)=some (readCfg M xs tail (b::buf)) := by
  simp [readCfg,TM2.step,code,readCode,TM2.stepAux,quote,clean,
    store_update_source,store_update_buffer]

 theorem read_nil (tail buf : List Bool) :
    (machine M).step (readCfg M [] tail buf)=some (loadCfg M tail buf []) := by
  simp [readCfg,loadCfg,TM2.step,code,readCode,TM2.stepAux,quote,clean,
    store_update_source,slot_nil]

 theorem read_run (xs tail buf : List Bool) :
    Trace (machine M).step (xs.length+1) (readCfg M xs tail buf) (loadCfg M tail (xs.reverse++buf) []) := by
  induction xs generalizing buf with
  | nil => exact Trace.cons (read_nil M tail buf) (Trace.refl _)
  | cons b xs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (read_cons M b xs tail buf) (ih (b::buf))

 theorem load_cons (b : Bool) (tail buf xs : List Bool) :
    (machine M).step (loadCfg M tail (b::buf) xs)=some (loadCfg M tail buf (b::xs)) := by
  simp [loadCfg,TM2.step,code,loadCode,TM2.stepAux,clean,
    store_update_buffer,store_update_local,slot_update,slot_self]

 theorem load_nil (tail xs : List Bool) :
    (machine M).step (loadCfg M tail [] xs)=some ((body M tail).cfg (M.initialCfg xs)) := by
  simp [loadCfg,Embedding.cfg,body,Machine.initialCfg,TM2.step,code,loadCode,TM2.stepAux,
    clean,store_update_buffer,slot]
  rfl

 theorem load_run (tail buf xs : List Bool) :
    Trace (machine M).step (buf.length+1) (loadCfg M tail buf xs)
      ((body M tail).cfg (M.initialCfg (buf.reverse++xs))) := by
  induction buf generalizing xs with
  | nil => exact Trace.cons (load_nil M tail xs) (Trace.refl _)
  | cons b bs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (load_cons M b tail bs xs) (ih (b::xs))

 theorem emit_cons (b : Bool) (tail xs buf : List Bool) :
    (machine M).step (emitCfg M tail (b::xs) buf)=some (emitCfg M tail xs (b::true::buf)) := by
  simp [emitCfg,TM2.step,code,emitCode,TM2.stepAux,clean,
    store_update_local,store_update_buffer,slot_update,slot_self]

 theorem emit_nil (tail buf : List Bool) :
    (machine M).step (emitCfg M tail [] buf)=some (drainCfg M tail (false::buf)) := by
  simp [emitCfg,drainCfg,TM2.step,code,emitCode,TM2.stepAux,clean,
    store_update_local,store_update_buffer,slot_nil]

 theorem emit_run (tail xs buf : List Bool) :
    Trace (machine M).step (xs.length+1) (emitCfg M tail xs buf)
      (drainCfg M tail ((quote xs).reverse++buf)) := by
  induction xs generalizing buf with
  | nil => exact Trace.cons (emit_nil M tail buf) (Trace.refl _)
  | cons b xs ih =>
      simpa only [List.length_cons,quote,List.reverse_cons,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using
        Trace.cons (emit_cons M b tail xs buf) (ih (b::true::buf))

 theorem drain_cons (b : Bool) (tail buf : List Bool) :
    (machine M).step (drainCfg M tail (b::buf))=some (drainCfg M (b::tail) buf) := by
  simp [drainCfg,TM2.step,code,drainCode,TM2.stepAux,clean,
    store_update_source,store_update_buffer]

 theorem drain_nil (tail : List Bool) :
    (machine M).step (drainCfg M tail [])=some ((machine M).finalCfg tail) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    rcases k with k | k <;> try cases k
    all_goals simp [Machine.finalCfg,code,drainCode,TM2.stepAux,clean]

 theorem drain_run (tail buf : List Bool) :
    Trace (machine M).step (buf.length+1) (drainCfg M tail buf) ((machine M).finalCfg (buf.reverse++tail)) := by
  induction buf generalizing tail with
  | nil => exact Trace.cons (drain_nil M tail) (Trace.refl _)
  | cons b bs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (drain_cons M b tail bs) (ih (b::tail))

 theorem body_final (tail xs : List Bool) : (body M tail).cfg (M.finalCfg xs)=emitCfg M tail xs [] := rfl

 theorem run {xs zs : List Bool} {n : ℕ} (tail : List Bool)
    (h : Trace M.step n (M.initialCfg xs) (M.finalCfg zs)) :
    Trace (machine M).step (2*xs.length+3*zs.length+5+n)
      ((machine M).initialCfg (quote xs++tail)) ((machine M).finalCfg (quote zs++tail)) := by
  have hi : (machine M).initialCfg (quote xs++tail)=readCfg M xs tail [] := by
    apply cfg_ext <;> try rfl
    funext k
    rcases k with k | k <;> try cases k
    all_goals simp [Machine.initialCfg,readCfg,store]
  rw [hi]
  have ha := read_run M xs tail []
  simp only [List.append_nil] at ha
  have hb := load_run M tail xs.reverse []
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at hb
  have hc := (body M tail).trace M.code (machine M).code (code_body M tail) h
  rw [body_final] at hc
  have hd := emit_run M tail zs []
  simp only [List.append_nil] at hd
  have he := drain_run M tail (quote zs).reverse
  simp only [List.reverse_reverse,List.length_reverse,quote_length] at he
  have hx := (((ha.trans hb).trans hc).trans hd).trans he
  convert hx using 1
  all_goals try with_reducible_and_instances rfl
  omega

end Thread

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
-- module Solutions.OAIQ053_KM.KMedian_Binary_BooleanProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace WordTransducer

def identity : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((),[b])
  finish _ := []

 theorem identity_run (xs : List Bool) : identity.run () xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b::identity.run () xs=b::xs; rw [ih]

def constant (s : List Bool) : Transducer where
  Q := Unit
  initial := ()
  next _ _ := ((),[])
  finish _ := s

 theorem constant_run (s xs : List Bool) : (constant s).run () xs=s := by
  induction xs with
  | nil => rfl
  | cons b xs ih => exact ih

 theorem duplicate_run (xs : List Bool) : duplicate.run () xs=(quote xs,xs) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change (true::b::(duplicate.run () xs).1,b::(duplicate.run () xs).2)=_
      rw [ih]
      rfl

 theorem exchange_done (xs : List Bool) : exchange.run (some true) xs=(quote xs,[]) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change (true::b::(exchange.run (some true) xs).1,(exchange.run (some true) xs).2)=_
      rw [ih]
      rfl

 theorem exchange_run (xs ys : List Bool) : exchange.run none (quote xs++ys)=(quote ys,xs) := by
  induction xs with
  | nil => exact exchange_done ys
  | cons b xs ih =>
      change ((exchange.run none (quote xs++ys)).1,b::(exchange.run none (quote xs++ys)).2)=_
      rw [ih]

end WordTransducer

namespace PolyProgram
variable {α β γ δ : Type}
variable {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool} {ed : δ → List Bool}
variable {f : α → β} {g : γ → δ}

noncomputable def identity (ea : α → List Bool) : PolyProgram ea ea _root_.id :=
  WordTransducer.identity.program.of_word (fun a => by
    simpa only [WordTransducer.identity,id_eq] using WordTransducer.identity_run (ea a))

noncomputable def constant (ea : α → List Bool) (eb : β → List Bool) (b : β) :
    PolyProgram ea eb (fun _ => b) :=
  (WordTransducer.constant (eb b)).program.of_word (fun a => by
    simpa only [WordTransducer.constant] using WordTransducer.constant_run (eb b) (ea a))

noncomputable def duplicate (ea : α → List Bool) : PolyProgram ea (encodePair ea ea) (fun a => (a,a)) :=
  WordTransducer.duplicate.program.of_word (fun a => by
    have h := congrArg (fun p : List Bool × List Bool => p.1++p.2) (WordTransducer.duplicate_run (ea a))
    simpa only [WordTransducer.duplicate,encodePair] using h)

noncomputable def exchange (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram (encodePair ea eb) (encodePair eb ea) Prod.swap :=
  WordTransducer.exchange.program.of_word (fun x => by
    have h := congrArg (fun p : List Bool × List Bool => p.1++p.2) (WordTransducer.exchange_run (ea x.1) (eb x.2))
    simpa only [WordTransducer.exchange,encodePair,Prod.swap] using h)

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
-- module Solutions.OAIQ053_KM.KMedian_Binary_BooleanListPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace WordTransducer

def emptyTest : Transducer where
  Q := Bool
  initial := true
  next _ _ := (false,[])
  finish b := [b]

 theorem emptyTest_run (q : Bool) (xs : List Bool) :
    emptyTest.run q xs=[q && xs.isEmpty] := by
  induction xs generalizing q with
  | nil => cases q <;> rfl
  | cons b xs ih =>
      change emptyTest.run false xs=_
      rw [ih]
      simp

def head : Transducer where
  Q := Option Bool
  initial := none
  next q b := (q.or (some b),[])
  finish q := [q.getD false]

 theorem head_run (q : Option Bool) (xs : List Bool) :
    head.run q xs=[(q.or xs.head?).getD false] := by
  induction xs generalizing q with
  | nil => cases q <;> rfl
  | cons b xs ih =>
      change head.run (q.or (some b)) xs=_
      rw [ih]
      cases q <;> rfl

 theorem prepend_done (xs : List Bool) : prepend.run 3 xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change b::prepend.run 3 xs=b::xs
      rw [ih]

 theorem prepend_run (b : Bool) (xs : List Bool) :
    prepend.run 0 (quote [b]++xs)=b::xs := by
  change b::prepend.run 3 xs=b::xs
  rw [prepend_done]

def prependWord (p : List Bool) : Transducer where
  Q := Bool
  initial := true
  next q b := (false,if q then p++[b] else [b])
  finish q := if q then p else []

 theorem prefix_done (p xs : List Bool) : (prependWord p).run false xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b::(prependWord p).run false xs=b::xs; rw [ih]

 theorem prefix_run (p xs : List Bool) : (prependWord p).run true xs=p++xs := by
  cases xs with
  | nil => exact (List.append_nil p).symm
  | cons b xs =>
      change (p++[b])++(prependWord p).run false xs=p++b::xs
      rw [prefix_done,List.append_assoc,List.singleton_append]

def select : Transducer where
  Q := Fin 2 ⊕ (Bool × Option (Option Bool))
  initial := .inl 0
  next q b := match q with
    | .inl k => if k=0 then (.inl 1,[]) else (.inr (b,none),[])
    | .inr (keep,none) => (.inr (keep,some none),[])
    | .inr (keep,some none) => (.inr (keep,some (some (!b))),[])
    | .inr (keep,some (some false)) => (.inr (keep,some none),if keep then [] else [b])
    | .inr (keep,some (some true)) => (.inr (keep,some (some true)),if keep then [b] else [])
  finish _ := []

 theorem select_done (keep : Bool) (xs : List Bool) :
    select.run (.inr (keep,some (some true))) xs=if keep then xs else [] := by
  induction xs with
  | nil => cases keep <;> rfl
  | cons b xs ih =>
      change (if keep then [b] else [])++select.run (.inr (keep,some (some true))) xs=_
      rw [ih]
      cases keep <;> simp

 theorem select_pair (keep : Bool) (xs ys : List Bool) :
    select.run (.inr (keep,some none)) (quote xs++ys)=if keep then ys else xs := by
  induction xs with
  | nil => exact select_done keep ys
  | cons b xs ih =>
      change (if keep then [] else [b])++select.run (.inr (keep,some none)) (quote xs++ys)=_
      rw [ih]
      cases keep <;> simp

 theorem select_run (keep : Bool) (xs ys : List Bool) :
    select.run (.inl 0) (quote [keep]++quote xs++ys)=if keep then ys else xs := by
  exact select_pair keep xs ys

end WordTransducer

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}

noncomputable def isEmpty : PolyProgram id encodeBool List.isEmpty :=
  WordTransducer.emptyTest.program.of_word (fun xs => by
    simpa only [WordTransducer.emptyTest,Bool.true_and,encodeBool,id_eq] using WordTransducer.emptyTest_run true xs)

noncomputable def head : PolyProgram id encodeBool (fun xs => xs.head?.getD false) :=
  WordTransducer.head.program.of_word (fun xs => by
    simpa only [WordTransducer.head,Option.or,encodeBool,id_eq] using WordTransducer.head_run none xs)

noncomputable def cons : PolyProgram (encodePair encodeBool id) id (fun x => x.1::x.2) :=
  WordTransducer.prepend.program.of_word (fun x => by
    simpa only [WordTransducer.prepend,encodePair,encodeBool,id_eq] using WordTransducer.prepend_run x.1 x.2)

noncomputable def prependWord (p : List Bool) : PolyProgram id id (fun xs => p++xs) :=
  (WordTransducer.prependWord p).program.of_word (fun xs => by
    simpa only [WordTransducer.prependWord,id_eq] using WordTransducer.prefix_run p xs)

noncomputable def injectLeft (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram eb (encodeLoop ea eb) Sum.inl :=
  (prependWord [false]).of_word (fun _ => rfl)

noncomputable def injectRight (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram ea (encodeLoop ea eb) Sum.inr :=
  (prependWord [true]).of_word (fun _ => rfl)

noncomputable def select (eb : β → List Bool) :
    PolyProgram (encodePair encodeBool (encodePair eb eb)) eb
      (fun x => if x.1 then x.2.2 else x.2.1) :=
  WordTransducer.select.program.of_word (fun x => by
    simpa only [WordTransducer.select,encodePair,encodeBool,List.append_assoc,apply_ite] using
      WordTransducer.select_run x.1 (eb x.2.1) (eb x.2.2))

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
-- module Solutions.OAIQ053_KM.KMedian_Binary_BooleanReverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace ReverseLoop
abbrev enc : S → List Bool := encodePair id id

end ReverseLoop

end MetricKMedian.Binary
end

end OAI
end


