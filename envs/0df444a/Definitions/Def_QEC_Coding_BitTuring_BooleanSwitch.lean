-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_BooleanSwitch
-- name    : QEC_Coding_BitTuring_BooleanSwitch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:57:29.539594+00:00
-- url     : https://prove2.me/theorems/a993b8aa-0ade-441f-99aa-102f1d70dae7
-- title:
--   Boolean Switch
-- statement:
--   Definitions and structural lemmas for Boolean Switch, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/BooleanSwitch.lean

import Definitions.Def_QEC_Coding_BitTuring_Composition
set_option autoImplicit false
namespace QEC.Coding.BitTuring.BooleanSwitch
open QEC.Coding.BitTuring Turing StateTransition
variable (A B:Machine)
abbrev Stack:=A.K⊕B.K
abbrev Label:=A.Λ⊕(B.Λ⊕Bool)
abbrev Var:=A.σ×B.σ×Bool
def stackB (k:B.K):Stack A B:=
 if k=B.input then .inl A.input else if k=B.output then .inl A.output else .inr k
def tapesA (S:A.K→List Bool):Stack A B→List Bool
 | .inl k=>S k
 | .inr _=>[]
def tapesB (S:B.K→List Bool):Stack A B→List Bool
 | .inl k=>if k=A.input then S B.input else if k=A.output then S B.output else []
 | .inr k=>if k=B.input ∨ k=B.output then [] else S k
def program:Label A B→TM2.Stmt (fun _:Stack A B=>Bool) (Label A B) (Var A B)
 | .inl l=>liftStatement Sum.inl Sum.inl Prod.fst
    (fun v w=>(w,v.2)) (some (.inr (.inr true))) (A.program l)
 | .inr (.inl l)=>liftStatement (stackB A B) (fun l=>.inr (.inl l))
    (fun v=>v.2.1) (fun v w=>(v.1,w,v.2.2)) (some (.inr (.inr true))) (B.program l)
 | .inr (.inr false)=>.pop (.inl A.input) (fun v h=>(v.1,v.2.1,h.getD false))
    (.branch (fun v=>v.2.2) (.goto fun _=>.inl A.main) (.goto fun _=>.inr (.inl B.main)))
 | .inr (.inr true)=>.load (fun _=>(A.initial,B.initial,false)) .halt
def machine:Machine where
 K:=Stack A B;input:=.inl A.input;output:=.inl A.output;Λ:=Label A B
 main:=.inr (.inr false);σ:=Var A B;initial:=(A.initial,B.initial,false);program:=program A B
def embedA:A.Cfg→(machine A B).Cfg:=
 liftCfg Sum.inl (fun v=>(v,B.initial,true)) (tapesA A B) (some (.inr (.inr true)))
def embedB:B.Cfg→(machine A B).Cfg:=
 liftCfg (fun l=>.inr (.inl l)) (fun v=>(A.initial,v,false))
  (tapesB A B) (some (.inr (.inr true)))
theorem tapesA_update (S:A.K→List Bool) (k:A.K) (w:List Bool):
 Function.update (tapesA A B S) (.inl k) w=tapesA A B (Function.update S k w):=by
 funext j;cases j with
 |inl j=>by_cases h:j=k <;> simp [tapesA,Function.update,h]
 |inr j=>simp [tapesA,Function.update]
theorem tapesB_read (ha:A.input≠A.output) (hb:B.input≠B.output) (S:B.K→List Bool) (k:B.K):
 tapesB A B S (stackB A B k)=S k:=by
 have hai:=Ne.symm ha;have hbi:=Ne.symm hb
 by_cases hi:k=B.input <;> by_cases ho:k=B.output <;> simp_all [stackB,tapesB]
theorem tapesB_update (ha:A.input≠A.output) (hb:B.input≠B.output)
 (S:B.K→List Bool) (k:B.K) (w:List Bool):
 Function.update (tapesB A B S) (stackB A B k) w=tapesB A B (Function.update S k w):=by
 funext j
 rw [Function.update_apply]
 cases j with
 |inl j=>
   simp only [tapesB]
   split_ifs with ji jo
   all_goals try rw [Function.update_apply]
   all_goals by_cases ki:k=B.input <;> by_cases ko:k=B.output
   all_goals simp_all [stackB,eq_comm]
 |inr j=>
   simp only [tapesB]
   split_ifs with hj
   all_goals try rw [Function.update_apply]
   all_goals by_cases ki:k=B.input <;> by_cases ko:k=B.output
   all_goals simp_all [stackB,eq_comm]
theorem stepAuxA (l:A.Λ) (v:A.σ) (S:A.K→List Bool):
 TM2.stepAux (program A B (.inl l)) (v,B.initial,true) (tapesA A B S)=
 embedA A B (TM2.stepAux (A.program l) v S):=
 stepAux_liftStatement (K:=A.K) (K':=Stack A B) (Λ:=A.Λ) (Λ':=Label A B)
  (σ:=A.σ) (σ':=Var A B) Sum.inl Sum.inl Prod.fst (fun v w=>(w,v.2))
  (some (.inr (.inr true))) (fun v=>(v,B.initial,true)) (tapesA A B)
  (fun _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl) (tapesA_update A B) (A.program l) v S
theorem stepAuxB (ha:A.input≠A.output) (hb:B.input≠B.output)
 (l:B.Λ) (v:B.σ) (S:B.K→List Bool):
 TM2.stepAux (program A B (.inr (.inl l))) (A.initial,v,false) (tapesB A B S)=
 embedB A B (TM2.stepAux (B.program l) v S):=
 stepAux_liftStatement (K:=B.K) (K':=Stack A B) (Λ:=B.Λ) (Λ':=Label A B)
  (σ:=B.σ) (σ':=Var A B) (stackB A B) (fun l=>.inr (.inl l))
  (fun v=>v.2.1) (fun v w=>(v.1,w,v.2.2)) (some (.inr (.inr true)))
  (fun v=>(A.initial,v,false)) (tapesB A B)
  (fun _=>rfl) (fun _ _=>rfl) (tapesB_read A B ha hb) (tapesB_update A B ha hb)
  (B.program l) v S
theorem stepA (c c':A.Cfg) (h:TM2.step A.program c=some c'):
 TM2.step (machine A B).program (embedA A B c)=some (embedA A B c'):=by
 rcases c with ⟨l,v,S⟩;cases l with
 |none=>simp [TM2.step] at h
 |some l=>
   have hh:TM2.stepAux (A.program l) v S=c':=Option.some.inj h
   rw [←hh];exact congrArg some (stepAuxA A B l v S)
theorem stepB (ha:A.input≠A.output) (hb:B.input≠B.output)
 (c c':B.Cfg) (h:TM2.step B.program c=some c'):
 TM2.step (machine A B).program (embedB A B c)=some (embedB A B c'):=by
 rcases c with ⟨l,v,S⟩;cases l with
 |none=>simp [TM2.step] at h
 |some l=>
   have hh:TM2.stepAux (B.program l) v S=c':=Option.some.inj h
   rw [←hh];exact congrArg some (stepAuxB A B ha hb l v S)
theorem startA (w:List Bool):
 TM2.step (machine A B).program ((machine A B).init (true::w))=
 some (embedA A B (A.init w)):=by
 simp [TM2.step,machine,program,Machine.init,TM2.stepAux,embedA,liftCfg,Function.update,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=A.input <;> simp_all [tapesA,Function.update]
 |inr j=>simp [tapesA,Function.update]
theorem startB (ha:A.input≠A.output) (hb:B.input≠B.output) (w:List Bool):
 TM2.step (machine A B).program ((machine A B).init (false::w))=
 some (embedB A B (B.init w)):=by
 have hai:=Ne.symm ha;have hbi:=Ne.symm hb
 simp [TM2.step,machine,program,Machine.init,TM2.stepAux,embedB,liftCfg,Function.update,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=A.input <;> by_cases ho:j=A.output <;>
   simp_all [tapesB,Function.update,eq_comm]
 |inr j=>by_cases hi:j=B.input <;> by_cases ho:j=B.output <;>
   simp_all [tapesB,Function.update,eq_comm]
theorem finishA (w:List Bool):
 TM2.step (machine A B).program (embedA A B (A.halt w))=
 some ((machine A B).halt w):=by
 simp [TM2.step,machine,program,Machine.halt,TM2.stepAux,embedA,liftCfg,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases ho:j=A.output <;> simp_all [tapesA,Function.update]
 |inr j=>simp [tapesA,Function.update]
theorem finishB (ha:A.input≠A.output) (hb:B.input≠B.output) (w:List Bool):
 TM2.step (machine A B).program (embedB A B (B.halt w))=
 some ((machine A B).halt w):=by
 have hai:=Ne.symm ha;have hbi:=Ne.symm hb
 simp [TM2.step,machine,program,Machine.halt,TM2.stepAux,embedB,liftCfg,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=A.input <;> by_cases ho:j=A.output <;>
   subst_vars <;> simp_all [tapesB,Function.update,eq_comm]
 |inr j=>by_cases hi:j=B.input <;> by_cases ho:j=B.output <;>
   subst_vars <;> simp_all [tapesB,Function.update,eq_comm]
def execA (w y:List Bool) (m:ℕ)
 (h:EvalsToInTime (TM2.step A.program) (A.init w) (some (A.halt y)) m):
 EvalsToInTime (TM2.step (machine A B).program) ((machine A B).init (true::w))
  (some ((machine A B).halt y)) (m+2):=by
 have hl:=iterate_lift (TM2.step A.program) (TM2.step (machine A B).program)
  (embedA A B) (stepA A B) _ _ _ h.evals_in_steps
 refine ⟨⟨1+h.steps+1,?_⟩,?_⟩
 · change (fun c:Option ((machine A B).Cfg)=>c.bind (TM2.step (machine A B).program))^[1+h.steps+1]
     (some ((machine A B).init (true::w)))=some ((machine A B).halt y)
   rw [Function.iterate_add_apply,Function.iterate_add_apply]
   simp only [Function.iterate_one,Option.bind_some,startA A B,hl,finishA A B]
 · change 1+h.steps+1≤ m+2
   have hh:=h.steps_le_m;omega
def execB (ha:A.input≠A.output) (hb:B.input≠B.output) (w y:List Bool) (m:ℕ)
 (h:EvalsToInTime (TM2.step B.program) (B.init w) (some (B.halt y)) m):
 EvalsToInTime (TM2.step (machine A B).program) ((machine A B).init (false::w))
  (some ((machine A B).halt y)) (m+2):=by
 have hl:=iterate_lift (TM2.step B.program) (TM2.step (machine A B).program)
  (embedB A B) (stepB A B ha hb) _ _ _ h.evals_in_steps
 refine ⟨⟨1+h.steps+1,?_⟩,?_⟩
 · change (fun c:Option ((machine A B).Cfg)=>c.bind (TM2.step (machine A B).program))^[1+h.steps+1]
     (some ((machine A B).init (false::w)))=some ((machine A B).halt y)
   rw [Function.iterate_add_apply,Function.iterate_add_apply]
   simp only [Function.iterate_one,Option.bind_some,startB A B ha hb,hl,finishB A B ha hb]
 · change 1+h.steps+1≤ m+2
   have hh:=h.steps_le_m;omega
end QEC.Coding.BitTuring.BooleanSwitch


