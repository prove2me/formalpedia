-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_CountedFlagLoop
-- name    : QEC_Coding_BitTuring_CountedFlagLoop
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:04:16.683283+00:00
-- url     : https://prove2.me/theorems/579ab215-295e-4d4a-a6f8-08752fa1b4ea
-- title:
--   Counted Flag Loop
-- statement:
--   Definitions and structural lemmas for Counted Flag Loop, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/CountedFlagLoop.lean

import Definitions.Def_QEC_Coding_BitTuring_FlagLoop
set_option autoImplicit false
namespace QEC.Coding.BitTuring.CountedFlagLoop
open Turing StateTransition
variable (A:Machine)
abbrev Stack:=FlagLoop.Stack A ⊕ Unit
abbrev Label:=FlagLoop.Label A ⊕ Fin 2
abbrev Var:=FlagLoop.Var A
def outputStack:Stack A:=.inl (.inr (.inr ()))
def counterStack:Stack A:=.inr ()
def tapes (C:List Bool) (S:FlagLoop.Stack A→List Bool):Stack A→List Bool
 | .inl k=>S k
 | .inr _=>C
def embed (C:List Bool):TM2.Cfg (fun _:FlagLoop.Stack A=>Bool) (FlagLoop.Label A) (FlagLoop.Var A)→
 TM2.Cfg (fun _:Stack A=>Bool) (Label A) (Var A):=
 liftCfg Sum.inl id (tapes A C) (some (.inr 0))
theorem tapes_update (C:List Bool) (S:FlagLoop.Stack A→List Bool) (k:FlagLoop.Stack A) (w:List Bool):
 Function.update (tapes A C S) (.inl k) w=tapes A C (Function.update S k w):=by
 funext j;cases j with
 | inl j=>by_cases h:j=k <;> simp [tapes,h]
 | inr j=>simp [tapes]
def lifted (l:FlagLoop.Label A):TM2.Stmt (fun _:Stack A=>Bool) (Label A) (Var A):=
 liftStatement Sum.inl Sum.inl id (fun _ w=>w) (some (.inr 0)) (FlagLoop.program A l)
def program:Label A→TM2.Stmt (fun _:Stack A=>Bool) (Label A) (Var A)
 | .inl (.inr 3)=>.branch (fun v=>v.2.1)
   (.load (fun _=>(A.initial,false,none)) (.goto fun _=>.inr 0))
   (.push (counterStack A) (fun _=>true)
     (.load (fun _=>(A.initial,false,none)) (.goto fun _=>.inl (.inl A.main))))
 | .inl l=>lifted A l
 | .inr 0=>.pop (outputStack A) (fun v h=>(v.1,v.2.1,h))
   (.branch (fun v=>v.2.2.isSome) (.goto fun _=>.inr 0) (.goto fun _=>.inr 1))
 | .inr _=>.pop (counterStack A) (fun v h=>(v.1,v.2.1,h))
   (.branch (fun v=>v.2.2.isSome)
    (.push (outputStack A) (fun v=>v.2.2.getD false) (.goto fun _=>.inr 1))
    (.load (fun _=>(A.initial,false,none)) .halt))
def machine:Machine where
 K:=Stack A;input:=.inl (.inl A.input);output:=outputStack A
 Λ:=Label A;main:=.inl (.inl A.main)
 σ:=Var A;initial:=(A.initial,false,none);program:=program A
def halt (w:List Bool):TM2.Cfg (fun _:Stack A=>Bool) (Label A) (Var A):=
 ⟨none,(A.initial,false,none),Function.update (fun _=>[]) (outputStack A) w⟩
theorem program_safe (l:FlagLoop.Label A) (hl:l≠.inr 3):program A (.inl l)=lifted A l:=by
 cases l with
 | inl l=>rfl
 | inr i=>fin_cases i <;> simp_all [program]
theorem stepAux_safe (C:List Bool) (l:FlagLoop.Label A) (hl:l≠.inr 3)
 (v:Var A) (S:FlagLoop.Stack A→List Bool):
 TM2.stepAux (program A (.inl l)) v (tapes A C S)=embed A C (TM2.stepAux (FlagLoop.program A l) v S):=by
 rw [program_safe A l hl]
 exact stepAux_liftStatement (K:=FlagLoop.Stack A) (K':=Stack A)
  (Λ:=FlagLoop.Label A) (Λ':=Label A) (σ:=Var A) (σ':=Var A)
  Sum.inl Sum.inl id (fun _ w=>w) (some (.inr 0)) id (tapes A C)
  (fun _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl) (tapes_update A C) (FlagLoop.program A l) v S
theorem step_safe (C:List Bool) (c c':TM2.Cfg (fun _:FlagLoop.Stack A=>Bool) (FlagLoop.Label A) (Var A))
 (hl:c.l≠some (.inr 3)) (h:TM2.step (FlagLoop.program A) c=some c'):
 TM2.step (program A) (embed A C c)=some (embed A C c'):=by
 rcases c with ⟨l,v,S⟩
 cases l with
 | none=>simp [TM2.step] at h
 | some l=>
  have hh:TM2.stepAux (FlagLoop.program A l) v S=c':=Option.some.inj h
  rw [←hh]
  change some (TM2.stepAux (program A (.inl l)) v (tapes A C S))=_
  exact congrArg some (stepAux_safe A C l (by simpa using hl) v S)
theorem stepBody (C:List Bool) (c c':A.Cfg) (h:TM2.step A.program c=some c'):
 TM2.step (program A) (embed A C (FlagLoop.embed A c))=some (embed A C (FlagLoop.embed A c')):=by
 apply step_safe A C _ _ ?_ (FlagLoop.step A c c' h)
 cases hl:c.l <;> simp [FlagLoop.embed,liftCfg,hl]
theorem stepCopy (hio:A.input≠A.output) (C:List Bool) (flag:Bool)
 (c c':TM2.Cfg (fun _:Fin 3=>Bool) Bool (Option Bool)) (h:TM2.step copyProgram c=some c'):
 TM2.step (program A) (embed A C (FlagLoop.embedCopy A flag c))=
 some (embed A C (FlagLoop.embedCopy A flag c')):=by
 rcases c with ⟨l,v,S⟩
 cases l with
 | none=>simp [TM2.step] at h
 | some l=>
  apply step_safe A C _ _ ?_ (FlagLoop.stepCopy A hio flag _ c' h)
  cases l <;> simp [FlagLoop.embedCopy,liftCfg,FlagLoop.copyLabel]
def start (x C:List Bool):TM2.Cfg (fun _:Stack A=>Bool) (Label A) (Var A):=
 embed A C ((FlagLoop.machine A).init x)
theorem header (C:List Bool) (flag:Bool) (w:List Bool):
 TM2.step (program A) (embed A C (FlagLoop.embed A (A.halt (flag::w))))=
 some (embed A C (FlagLoop.embedCopy A flag (copyCfg true w [] [] none))):=by
 apply step_safe A C _ _ ?_ (FlagLoop.header A flag w)
 simp [FlagLoop.embed,liftCfg,Machine.halt]
theorem before_finish (hio:A.input≠A.output) (C:List Bool) (flag:Bool) (w:List Bool):
 (fun c=>c.bind (TM2.step (program A)))^[2*w.length+3]
  (some (embed A C (FlagLoop.embed A (A.halt (flag::w)))))=
 some (embed A C (FlagLoop.embedCopy A flag (copyHalt w))):=by
 have hc:=iterate_lift (TM2.step copyProgram) (TM2.step (program A))
  (fun c=>embed A C (FlagLoop.embedCopy A flag c)) (stepCopy A hio C flag) _ _ _ (copyRun w)
 rw [show 2*w.length+3=(2*w.length+2)+1 by omega,Function.iterate_succ_apply]
 simp only [Option.bind_some,header]
 exact hc
end QEC.Coding.BitTuring.CountedFlagLoop
namespace QEC.Coding.BitTuring.CountedFlagLoop
open Turing StateTransition
variable (A:Machine)
def next (c:Option (TM2.Cfg (fun _:Stack A=>Bool) (Label A) (Var A))):=c.bind (TM2.step (program A))
def finishTapes (w C:List Bool):Stack A→List Bool
 | .inl k=>if k=(.inr (.inr ()) : FlagLoop.Stack A) then w else []
 | .inr _=>C
theorem finishTapes_read_output (w C:List Bool):finishTapes A w C (outputStack A)=w:=by
 simp [finishTapes,outputStack]
theorem finishTapes_read_counter (w C:List Bool):finishTapes A w C (counterStack A)=C:=rfl
def finishCfg (l:Fin 2) (v:Option Bool) (w C:List Bool):TM2.Cfg (fun _:Stack A=>Bool) (Label A) (Var A):=
 ⟨some (.inr l),(A.initial,false,v),finishTapes A w C⟩
theorem finishTapes_output (w C z:List Bool):
 Function.update (finishTapes A w C) (outputStack A) z=finishTapes A z C:=by
 funext k;cases k with
 | inl k=>
  by_cases h:k=(.inr (.inr ()) : FlagLoop.Stack A)
  · subst k;simp [finishTapes,outputStack,Function.update]
  · simp [finishTapes,outputStack,Function.update,h]
 | inr k=>simp [finishTapes,outputStack,Function.update]
theorem finishTapes_counter (w C z:List Bool):
 Function.update (finishTapes A w C) (counterStack A) z=finishTapes A w z:=by
 funext k;cases k with
 | inl k=>simp [finishTapes,counterStack,Function.update]
 | inr k=>cases k;simp [finishTapes,counterStack,Function.update]
theorem drain_cons (v:Option Bool) (b:Bool) (w C:List Bool):
 next A (some (finishCfg A 0 v (b::w) C))=some (finishCfg A 0 (some b) w C):=by
 simp [next,TM2.step,program,finishCfg,TM2.stepAux,finishTapes_read_output,finishTapes_output]
theorem drain_nil (v:Option Bool) (C:List Bool):
 next A (some (finishCfg A 0 v [] C))=some (finishCfg A 1 none [] C):=by
 simp [next,TM2.step,program,finishCfg,TM2.stepAux,finishTapes_read_output,finishTapes_output]
theorem counter_cons (v:Option Bool) (b:Bool) (w C:List Bool):
 next A (some (finishCfg A 1 v w (b::C)))=some (finishCfg A 1 (some b) (b::w) C):=by
 simp [next,TM2.step,program,finishCfg,TM2.stepAux,finishTapes_read_output,finishTapes_read_counter,finishTapes_counter,finishTapes_output]
theorem counter_nil (v:Option Bool) (w:List Bool):
 next A (some (finishCfg A 1 v w []))=some (halt A w):=by
 simp [next,TM2.step,program,finishCfg,TM2.stepAux,finishTapes_read_counter,finishTapes_counter,halt,TM2.Cfg.mk.injEq]
 funext k;cases k with
 | inl k=>
  by_cases h:k=(.inr (.inr ()) : FlagLoop.Stack A)
  · subst k;simp [finishTapes,outputStack,Function.update]
  · simp [finishTapes,outputStack,Function.update,h]
 | inr k=>simp [finishTapes,outputStack,Function.update]
theorem drainRun (v:Option Bool) (w C:List Bool):
 (next A)^[w.length+1] (some (finishCfg A 0 v w C))=some (finishCfg A 1 none [] C):=by
 induction w generalizing v with
 | nil=>simpa only [List.length_nil,Nat.zero_add,Function.iterate_one] using drain_nil A v C
 | cons b w ih=>
  rw [List.length_cons,Function.iterate_succ_apply,drain_cons]
  exact ih (some b)
theorem counterRun (v:Option Bool) (w C:List Bool):
 (next A)^[C.length+1] (some (finishCfg A 1 v w C))=some (halt A (C.reverse++w)):=by
 induction C generalizing v w with
 | nil=>simpa only [List.length_nil,Nat.zero_add,List.reverse_nil,List.nil_append,Function.iterate_one] using counter_nil A v w
 | cons b C ih=>
  rw [List.length_cons,Function.iterate_succ_apply,counter_cons]
  simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using ih (some b) (b::w)
theorem finishRun (w C:List Bool):
 (next A)^[w.length+C.length+2] (some (finishCfg A 0 none w C))=some (halt A C.reverse):=by
 rw [show w.length+C.length+2=(C.length+1)+(w.length+1) by omega,Function.iterate_add_apply,drainRun]
 simpa only [List.append_nil] using counterRun A none [] C
end QEC.Coding.BitTuring.CountedFlagLoop
namespace QEC.Coding.BitTuring.CountedFlagLoop
open Turing StateTransition
variable (A:Machine)
theorem finish_false (hio:A.input≠A.output) (w C:List Bool):
 next A (some (embed A C (FlagLoop.embedCopy A false (copyHalt w))))=some (start A w (true::C)):=by
 simp [next,TM2.step,program,embed,liftCfg,FlagLoop.embedCopy,FlagLoop.copyLabel,
  copyHalt,TM2.stepAux,start,FlagLoop.machine,Machine.init,TM2.Cfg.mk.injEq]
 funext k;cases k with
 | inl k=>cases k with
  | inl k=>
   by_cases ho:k=A.output <;> by_cases hi:k=A.input <;>
    simp_all [tapes,FlagLoop.copyTapes,counterStack,Function.update]
  | inr k=>cases k with
   | inl k=>cases k;simp [tapes,FlagLoop.copyTapes,counterStack,Function.update]
   | inr k=>cases k;simp [tapes,FlagLoop.copyTapes,counterStack,Function.update]
 | inr k=>cases k;simp [tapes,counterStack,Function.update]
theorem finish_true (w C:List Bool):
 next A (some (embed A C (FlagLoop.embedCopy A true (copyHalt w))))=some (finishCfg A 0 none w C):=by
 simp [next,TM2.step,program,embed,liftCfg,FlagLoop.embedCopy,FlagLoop.copyLabel,
  copyHalt,TM2.stepAux,finishCfg,TM2.Cfg.mk.injEq]
 funext k;cases k with
 | inl k=>cases k with
  | inl k=>simp [tapes,FlagLoop.copyTapes,finishTapes]
  | inr k=>cases k with
   | inl k=>cases k;simp [tapes,FlagLoop.copyTapes,finishTapes]
   | inr k=>cases k;simp [tapes,FlagLoop.copyTapes,finishTapes]
 | inr k=>simp [tapes,finishTapes]
theorem transfer_false (hio:A.input≠A.output) (w C:List Bool):
 (next A)^[2*w.length+4] (some (embed A C (FlagLoop.embed A (A.halt (false::w)))))=
 some (start A w (true::C)):=by
 rw [show 2*w.length+4=1+(2*w.length+3) by omega,Function.iterate_add_apply]
 rw [show next A=(fun c=>c.bind (TM2.step (program A))) from rfl,before_finish A hio C false w]
 exact finish_false A hio w C
theorem transfer_true (hio:A.input≠A.output) (w C:List Bool):
 (next A)^[3*w.length+C.length+6] (some (embed A C (FlagLoop.embed A (A.halt (true::w)))))=
 some (halt A C.reverse):=by
 have hb:(next A)^[1+(2*w.length+3)]
   (some (embed A C (FlagLoop.embed A (A.halt (true::w)))))=some (finishCfg A 0 none w C):=by
  rw [Function.iterate_add_apply]
  change next A ((next A)^[2*w.length+3] (some (embed A C (FlagLoop.embed A (A.halt (true::w))))))=_
  rw [show next A=(fun c=>c.bind (TM2.step (program A))) from rfl,before_finish A hio C true w]
  exact finish_true A w C
 rw [show 3*w.length+C.length+6=(w.length+C.length+2)+(1+(2*w.length+3)) by omega,
  Function.iterate_add_apply,hb]
 exact finishRun A w C
end QEC.Coding.BitTuring.CountedFlagLoop
namespace QEC.Coding.BitTuring.CountedFlagLoop
open Turing StateTransition
variable (A:Machine)
def continueExec (hio:A.input≠A.output) (x w C:List Bool) (a:ℕ)
 (hA:EvalsToInTime (TM2.step A.program) (A.init x) (some (A.halt (false::w))) a):
 EvalsToInTime (TM2.step (program A)) (start A x C) (some (start A w (true::C)))
 (a+2*w.length+4):=by
 refine ⟨⟨(2*w.length+4)+hA.steps,?_⟩,?_⟩
 · have hr:=iterate_lift (TM2.step A.program) (TM2.step (program A))
    (fun c=>embed A C (FlagLoop.embed A c)) (stepBody A C) _ _ _ hA.evals_in_steps
   have he:embed A C (FlagLoop.embed A (A.init x))=start A x C:=by rw [FlagLoop.embed_init];rfl
   change (next A)^[(_)+hA.steps] (some (start A x C))=_
   rw [←he,Function.iterate_add_apply]
   change (next A)^[hA.steps] (some (embed A C (FlagLoop.embed A (A.init x))))=_ at hr
   rw [hr]
   exact transfer_false A hio w C
 · change (2*w.length+4)+hA.steps≤ a+2*w.length+4
   have h:=hA.steps_le_m;omega
def terminalExec (hio:A.input≠A.output) (x w C:List Bool) (a:ℕ)
 (hA:EvalsToInTime (TM2.step A.program) (A.init x) (some (A.halt (true::w))) a):
 EvalsToInTime (TM2.step (program A)) (start A x C) (some (halt A C.reverse))
 (a+3*w.length+C.length+6):=by
 refine ⟨⟨(3*w.length+C.length+6)+hA.steps,?_⟩,?_⟩
 · have hr:=iterate_lift (TM2.step A.program) (TM2.step (program A))
    (fun c=>embed A C (FlagLoop.embed A c)) (stepBody A C) _ _ _ hA.evals_in_steps
   have he:embed A C (FlagLoop.embed A (A.init x))=start A x C:=by rw [FlagLoop.embed_init];rfl
   change (next A)^[(_)+hA.steps] (some (start A x C))=_
   rw [←he,Function.iterate_add_apply]
   change (next A)^[hA.steps] (some (embed A C (FlagLoop.embed A (A.init x))))=_ at hr
   rw [hr]
   exact transfer_true A hio w C
 · change (3*w.length+C.length+6)+hA.steps≤ a+3*w.length+C.length+6
   have h:=hA.steps_le_m;omega
end QEC.Coding.BitTuring.CountedFlagLoop


