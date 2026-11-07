-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_SuffixJoin
-- name    : QEC_Coding_BitTuring_SuffixJoin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T21:29:37.570926+00:00
-- url     : https://prove2.me/theorems/6a38fa64-ca23-4d3c-b2e4-97d1d49a4cd7
-- title:
--   Suffix Join
-- statement:
--   Definitions and structural lemmas for Suffix Join, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/SuffixJoin.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_RetainedInput
set_option autoImplicit false
namespace QEC.Coding.BitTuring.SuffixJoin
open QEC.Coding.BitTuring Turing StateTransition
variable (A:Machine)
abbrev Stack:=A.K⊕Unit
abbrev Label:=A.Λ⊕Fin 3
abbrev Var:=A.σ×Option Bool
def program:Label A→TM2.Stmt (fun _:Stack A=>Bool) (Label A) (Var A)
 | .inl l=>liftStatement Sum.inl Sum.inl Prod.fst (fun v w=>(w,v.2))
     (some (.inr 0)) (A.program l)
 | .inr k=>if k=0 then
     .pop (.inl A.output) (fun v h=>(v.1,h)) (.branch (fun v=>v.2.isSome)
       (.push (.inr ()) (fun v=>v.2.getD false) (.goto fun _=>.inr 0))
       (.push (.inr ()) (fun _=>false) (.goto fun _=>.inr 1)))
   else if k=1 then
     .pop (.inl A.input) (fun v h=>(v.1,h)) (.branch (fun v=>v.2.isSome)
       (.push (.inr ()) (fun v=>v.2.getD false) (.goto fun _=>.inr 1))
       (.goto fun _=>.inr 2))
   else .pop (.inr ()) (fun v h=>(v.1,h)) (.branch (fun v=>v.2.isSome)
       (.push (.inl A.output) (fun v=>v.2.getD false) (.goto fun _=>.inr 2))
       (.load (fun _=>(A.initial,none)) .halt))
def machine:Machine where
 K:=Stack A;input:=.inl A.input;output:=.inl A.output;Λ:=Label A;main:=.inl A.main
 σ:=Var A;initial:=(A.initial,none);program:=program A
def tapes (S:A.K→List Bool):Stack A→List Bool
 | .inl k=>S k
 | .inr _=>[]
def embed:A.Cfg→TM2.Cfg (fun _:Stack A=>Bool) (Label A) (Var A):=
 liftCfg Sum.inl (fun v=>(v,none)) (tapes A) (some (.inr 0))
theorem tapes_update (S:A.K→List Bool) (k:A.K) (w:List Bool):
 Function.update (tapes A S) (.inl k) w=tapes A (Function.update S k w):=by
 funext j;cases j with
 |inl j=>by_cases h:j=k <;> simp [tapes,Function.update,h]
 |inr j=>simp [tapes,Function.update]
theorem stepAux (l:A.Λ) (v:A.σ) (S:A.K→List Bool):
 TM2.stepAux (program A (.inl l)) (v,none) (tapes A S)=embed A (TM2.stepAux (A.program l) v S):=
 stepAux_liftStatement (K:=A.K) (K':=Stack A) (Λ:=A.Λ) (Λ':=Label A) (σ:=A.σ) (σ':=Var A)
  Sum.inl Sum.inl Prod.fst (fun v w=>(w,v.2)) (some (.inr 0)) (fun v=>(v,none)) (tapes A)
  (fun _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl) (tapes_update A) (A.program l) v S
theorem step (c c':A.Cfg) (h:TM2.step A.program c=some c'):
 TM2.step (program A) (embed A c)=some (embed A c'):=by
 rcases c with ⟨l,v,S⟩;cases l with
 |none=>simp [TM2.step] at h
 |some l=>
  have hh:TM2.stepAux (A.program l) v S=c':=Option.some.inj h
  rw [←hh];exact congrArg some (stepAux A l v S)
def cfg (k:Fin 3) (x y b:List Bool) (v:Option Bool):
 TM2.Cfg (fun _:Stack A=>Bool) (Label A) (Var A):=
 ⟨some (.inr k),(A.initial,v),fun j=>match j with
 | .inl j=>DrainInput.tapes A x y j
 | .inr _=>b⟩
theorem out_cons (hio:A.input≠A.output) (x y b:List Bool) (a:Bool) (v:Option Bool):
 TM2.step (program A) (cfg A 0 x (a::y) b v)=some (cfg A 0 x y (a::b) (some a)):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,Ne.symm hio,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=A.input <;> by_cases ho:j=A.output <;> simp_all [Function.update]
 |inr j=>simp [Function.update]
theorem out_nil (hio:A.input≠A.output) (x b:List Bool) (v:Option Bool):
 TM2.step (program A) (cfg A 0 x [] b v)=some (cfg A 1 x [] (false::b) none):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,Ne.symm hio,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=A.input <;> by_cases ho:j=A.output <;> simp_all [Function.update]
 |inr j=>simp [Function.update]
theorem out_run (hio:A.input≠A.output) (x y b:List Bool) (v:Option Bool):
 (fun c=>c.bind (TM2.step (program A)))^[y.length+1] (some (cfg A 0 x y b v))=
   some (cfg A 1 x [] (false::(y.reverse++b)) none):=by
 induction y generalizing b v with
 |nil=>simpa using out_nil A hio x b v
 |cons a y ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,out_cons A hio]
  rw [ih];simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
theorem tail_cons (_hio:A.input≠A.output) (x b:List Bool) (a:Bool) (v:Option Bool):
 TM2.step (program A) (cfg A 1 (a::x) [] b v)=some (cfg A 1 x [] (a::b) (some a)):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=A.input <;> by_cases ho:j=A.output <;> simp_all [Function.update]
 |inr j=>simp [Function.update]
theorem tail_nil (_hio:A.input≠A.output) (b:List Bool) (v:Option Bool):
 TM2.step (program A) (cfg A 1 [] [] b v)=some (cfg A 2 [] [] b none):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes]
theorem tail_run (hio:A.input≠A.output) (x b:List Bool) (v:Option Bool):
 (fun c=>c.bind (TM2.step (program A)))^[x.length+1] (some (cfg A 1 x [] b v))=
   some (cfg A 2 [] [] (x.reverse++b) none):=by
 induction x generalizing b v with
 |nil=>simpa using tail_nil A hio b v
 |cons a x ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,tail_cons A hio]
  rw [ih];simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
theorem reverse_cons (hio:A.input≠A.output) (y b:List Bool) (a:Bool) (v:Option Bool):
 TM2.step (program A) (cfg A 2 [] y (a::b) v)=some (cfg A 2 [] (a::y) b (some a)):=by
 simp [TM2.step,program,cfg,TM2.stepAux,DrainInput.tapes,Ne.symm hio,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=A.input <;> by_cases ho:j=A.output <;> simp_all [Function.update]
 |inr j=>simp [Function.update]
theorem reverse_nil (hio:A.input≠A.output) (y:List Bool) (v:Option Bool):
 TM2.step (program A) (cfg A 2 [] y [] v)=some ((machine A).halt y):=by
 simp [TM2.step,program,cfg,TM2.stepAux,Machine.halt,machine,DrainInput.tapes,Ne.symm hio,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=A.input <;> by_cases ho:j=A.output <;> simp_all [Function.update]
 |inr j=>simp [Function.update]
theorem reverse_run (hio:A.input≠A.output) (y b:List Bool) (v:Option Bool):
 (fun c=>c.bind (TM2.step (program A)))^[b.length+1] (some (cfg A 2 [] y b v))=
   some ((machine A).halt (b.reverse++y)):=by
 induction b generalizing y v with
 |nil=>simpa using reverse_nil A hio y v
 |cons a b ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,reverse_cons A hio]
  rw [ih];simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
  rfl
theorem partial_eq (x y:List Bool):embed A (DrainInput.partialHalt A x y)=cfg A 0 x y [] none:=rfl
theorem init_eq (w:List Bool):(machine A).init w=embed A (A.init w):=by
 simp [Machine.init,machine,embed,liftCfg,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>simp [tapes,Function.update]
 |inr j=>simp [tapes,Function.update]
def exec (hio:A.input≠A.output) (w x y:List Bool) (m:ℕ)
 (h:EvalsToInTime (TM2.step A.program) (A.init w) (some (DrainInput.partialHalt A x y)) m):
 EvalsToInTime (TM2.step (machine A).program) ((machine A).init w)
  (some ((machine A).halt (y++false::x))) (m+2*(x.length+y.length)+4):=by
 have hl:=iterate_lift (TM2.step A.program) (TM2.step (program A)) (embed A) (step A)
   _ _ _ h.evals_in_steps
 let b:=x.reverse++[false]++y.reverse
 refine ⟨⟨(b.length+1)+(x.length+1)+(y.length+1)+h.steps,?_⟩,?_⟩
 · rw [init_eq]
   change (fun c:Option (TM2.Cfg (fun _:Stack A=>Bool) (Label A) (Var A))=>c.bind (TM2.step (program A)))^[(b.length+1)+(x.length+1)+(y.length+1)+h.steps]
     (some (embed A (A.init w)))=some ((machine A).halt (y++false::x))
   rw [Function.iterate_add_apply,hl,partial_eq,Function.iterate_add_apply,out_run A hio,
     Function.iterate_add_apply,tail_run A hio]
   simp only [List.append_nil]
   have he:x.reverse++false::y.reverse=b:=by dsimp [b];simp only [List.append_assoc,List.singleton_append]
   rw [he,reverse_run A hio]
   simp only [b,List.reverse_append,List.reverse_cons,List.reverse_reverse,List.append_nil,List.append_assoc,List.singleton_append]
   rfl
 · change (b.length+1)+(x.length+1)+(y.length+1)+h.steps≤ m+2*(x.length+y.length)+4
   have hs:=h.steps_le_m
   simp only [b,List.length_append,List.length_reverse,List.length_singleton]
   omega
end QEC.Coding.BitTuring.SuffixJoin


