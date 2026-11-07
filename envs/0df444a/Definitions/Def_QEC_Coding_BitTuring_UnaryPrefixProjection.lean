-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
-- name    : QEC_Coding_BitTuring_UnaryPrefixProjection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:07:37.145218+00:00
-- url     : https://prove2.me/theorems/4e6c7325-9d19-44da-83fb-936bc97f3795
-- title:
--   Unary Prefix Projection
-- statement:
--   Definitions and structural lemmas for Unary Prefix Projection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryPrefixProjection.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length

set_option autoImplicit false
namespace QEC.Coding.BitTuring.DrainInput
open QEC.Coding.BitTuring Turing StateTransition
variable (A:Machine)
abbrev Label:=A.Λ⊕Unit
abbrev Var:=A.σ×Option Bool
def program : Label A→TM2.Stmt (fun _:A.K=>Bool) (Label A) (Var A)
  | .inl l=>liftStatement id Sum.inl Prod.fst (fun v w=>(w,v.2)) (some (.inr ())) (A.program l)
  | .inr _=>.pop A.input (fun v h=>(v.1,h)) (.branch (fun v=>v.2.isSome)
      (.goto fun _=>.inr ()) (.load (fun _=>(A.initial,none)) .halt))
def machine : Machine where
  K:=A.K;input:=A.input;output:=A.output;Λ:=Label A;main:=.inl A.main
  σ:=Var A;initial:=(A.initial,none);program:=program A
def embed : A.Cfg→TM2.Cfg (fun _:A.K=>Bool) (Label A) (Var A) :=
  liftCfg Sum.inl (fun v=>(v,none)) id (some (.inr ()))
theorem stepAux (l:A.Λ) (v:A.σ) (S:A.K→List Bool) :
    TM2.stepAux (program A (.inl l)) (v,none) S=embed A (TM2.stepAux (A.program l) v S) :=
  stepAux_liftStatement (K:=A.K) (K':=A.K) (Λ:=A.Λ) (Λ':=Label A) (σ:=A.σ) (σ':=Var A)
    id Sum.inl Prod.fst (fun v w=>(w,v.2)) (some (.inr ())) (fun v=>(v,none)) id
    (fun _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl) (fun _ _ _=>rfl) (A.program l) v S
theorem step (c c':A.Cfg) (h:TM2.step A.program c=some c') :
    TM2.step (program A) (embed A c)=some (embed A c') :=by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none=>simp [TM2.step] at h
  | some l=>
    have hh:TM2.stepAux (A.program l) v S=c':=Option.some.inj h
    rw [←hh]
    exact congrArg some (stepAux A l v S)
def tapes (x y:List Bool) (k:A.K):List Bool :=
  if k=A.input then x else if k=A.output then y else []
def partialHalt (x y:List Bool):A.Cfg:=⟨none,A.initial,tapes A x y⟩
def drainCfg (x y:List Bool) (v:Option Bool):
    TM2.Cfg (fun _:A.K=>Bool) (Label A) (Var A):=⟨some (.inr ()),(A.initial,v),tapes A x y⟩
theorem embed_partial (x y:List Bool):embed A (partialHalt A x y)=drainCfg A x y none:=rfl
theorem drain_cons (b:Bool) (x y:List Bool) (v:Option Bool):
    TM2.step (program A) (drainCfg A (b::x) y v)=some (drainCfg A x y (some b)) :=by
  simp [TM2.step,program,drainCfg,tapes,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k
  by_cases hk:k=A.input <;> simp [tapes,Function.update,hk]
theorem drain_nil (hio:A.input≠A.output) (y:List Bool) (v:Option Bool):
    TM2.step (program A) (drainCfg A [] y v)=some ((machine A).halt y) :=by
  simp [TM2.step,program,drainCfg,tapes,TM2.stepAux,Machine.halt,machine,TM2.Cfg.mk.injEq]
  funext k
  by_cases hi:k=A.input
  · subst k;simp [Function.update,hio]
  · by_cases ho:k=A.output <;> simp [tapes,Function.update,hi,ho,Ne.symm hio]
theorem drain_run (hio:A.input≠A.output) (x y:List Bool) (v:Option Bool):
    (fun c=>c.bind (TM2.step (program A)))^[x.length+1] (some (drainCfg A x y v))=
      some ((machine A).halt y) :=by
  induction x generalizing v with
  | nil=>
    simpa only [List.length_nil,Nat.zero_add,Function.iterate_one,Option.bind_some] using drain_nil A hio y v
  | cons b x ih=>
    rw [List.length_cons,Nat.add_right_comm,Function.iterate_succ_apply]
    simp only [Option.bind_some,drain_cons]
    exact ih (some b)
theorem init_eq (x:List Bool):(machine A).init x=embed A (A.init x):=rfl
def executes (hio:A.input≠A.output) (w x y:List Bool) (m:ℕ)
    (h:EvalsToInTime (TM2.step A.program) (A.init w) (some (partialHalt A x y)) m) :
    EvalsToInTime (TM2.step (machine A).program) ((machine A).init w)
      (some ((machine A).halt y)) (m+x.length+1) :=by
  have hl:=iterate_lift (TM2.step A.program) (TM2.step (program A)) (embed A) (step A)
    _ _ _ h.evals_in_steps
  refine ⟨⟨(x.length+1)+h.steps,?_⟩,?_⟩
  · rw [init_eq]
    change (fun c:Option (TM2.Cfg (fun _:A.K=>Bool) (Label A) (Var A))=>c.bind (TM2.step (program A)))^[(x.length+1)+h.steps]
      (some (embed A (A.init w)))=some ((machine A).halt y)
    rw [Function.iterate_add_apply,hl,embed_partial,drain_run A hio]
  · change (x.length + 1) + h.steps ≤ m + x.length + 1
    have:=h.steps_le_m
    omega
end QEC.Coding.BitTuring.DrainInput
namespace QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)
def suffixHalt (s y:List Bool):TM2.Cfg (fun _:Fin 3=>Bool) (FieldProjection.Label n) (Option Bool):=
   ⟨none,none,![s,[],y]⟩
theorem reverse_cons (s:List Bool) (x:Bool) (b d:List Bool) (v:Option Bool):
    TM2.step (program n keep) (revCfg n s (x::b) d v)=some (revCfg n s b (x::d) (some x)) :=by
  simp [TM2.step,program,revCfg,copyProgram,liftStatement,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem reverse_nil (s d:List Bool) (v:Option Bool):
    TM2.step (program n keep) (revCfg n s [] d v)=some (suffixHalt n s d) :=by
  simp [TM2.step,program,revCfg,suffixHalt,copyProgram,liftStatement,TM2.stepAux,TM2.Cfg.mk.injEq]
theorem reverse_run (s b d:List Bool) (v:Option Bool):
    (fun c=>c.bind (TM2.step (program n keep)))^[b.length+1] (some (revCfg n s b d v))=
      some (suffixHalt n s (b.reverse++d)) :=by
  induction b generalizing d v with
  | nil=>simp [reverse_nil]
  | cons x b ih=>
    simp only [List.length_cons]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,reverse_cons]
    rw [ih];simp [List.reverse_cons,List.append_assoc]
theorem parse_fields (xs:List ℕ) (k:Fin (n+1)) (hk:k.val+xs.length=n+1) (hne:xs≠[])
    (s b d:List Bool) (v:Option Bool):
    (fun c=>c.bind (TM2.step (program n keep)))^[(stream xs).length]
      (some (cfg n k (stream xs++s) b d v))=
      some (revCfg n s (buffer n keep k.val xs b).tail d none) :=by
  induction xs generalizing k b d v with
  | nil=>exact False.elim (hne rfl)
  | cons a xs ih=>
    cases xs with
    | nil=>
      have hkl:k.val=n:=by simp only [List.length_cons,List.length_nil] at hk;omega
      have h:=field_last n keep k hkl a s b d v
      simpa only [stream,List.length_append,List.length_cons,List.length_nil,unary_length,
        List.append_nil,List.cons_append,List.nil_append,List.append_assoc,buffer,maskAt_val] using h
    | cons c xs=>
      have hkl:k.val<n:=by simp only [List.length_cons] at hk;omega
      rw [show (stream (a::c::xs)).length=(stream (c::xs)).length+(a+1) by
        change (unary a++false::stream (c::xs)).length=_
        simp only [List.length_append,List.length_cons,unary_length];omega]
      rw [show stream (a::c::xs)++s=unary a++false::(stream (c::xs)++s) by
        simp only [stream,List.append_assoc,List.cons_append]]
      change (fun c=>c.bind (TM2.step (program n keep)))^[(stream (c::xs)).length+(a+1)]
        (some (cfg n k (unary a++false::(stream (c::xs)++s)) b d v))=_
      rw [Function.iterate_add_apply,field_lt n keep k hkl]
      have htail:(⟨k.val+1,Nat.succ_lt_succ hkl⟩:Fin (n+1)).val+(c::xs).length=n+1:=by
        simp only [List.length_cons] at hk ⊢;omega
      have h:=ih ⟨k.val+1,Nat.succ_lt_succ hkl⟩ htail (by simp)
        (if keep k then false::(unary a++b) else b) d (some false)
      simpa only [buffer,maskAt_val] using h
theorem init_eq (xs:List ℕ) (s:List Bool):(FieldProjection.machine n keep).init (stream xs++s)=
    cfg n 0 (stream xs++s) [] [] none :=by
  simp [Machine.init,FieldProjection.machine,cfg,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem partial_run (xs:List ℕ) (hx:xs.length=n+1) (s:List Bool):
    (fun c=>c.bind (TM2.step (FieldProjection.machine n keep).program))^[steps n keep xs]
      (some ((FieldProjection.machine n keep).init (stream xs++s)))=
      some (suffixHalt n s (raw (fields n keep 0 xs))) :=by
  rw [init_eq]
  change (fun c:Option (TM2.Cfg (fun _:Fin 3=>Bool) (FieldProjection.Label n) (Option Bool))=>
    c.bind (TM2.step (program n keep)))^[steps n keep xs] (some (cfg n 0 (stream xs++s) [] [] none))=_
  rw [show steps n keep xs=((buffer n keep 0 xs []).tail.length+1)+(stream xs).length by
    simp only [steps];omega,Function.iterate_add_apply,
    parse_fields n keep xs 0 (by simpa using hx) (by intro h;subst xs;simp at hx)]
  have h:=reverse_run n keep s (buffer n keep 0 xs []).tail [] none
  rw [buffer_output,List.append_nil] at h
  exact h
theorem suffixHalt_eq (s y:List Bool):suffixHalt n s y=
    QEC.Coding.BitTuring.DrainInput.partialHalt (FieldProjection.machine n keep) s y :=by
  simp [suffixHalt,QEC.Coding.BitTuring.DrainInput.partialHalt,
    FieldProjection.machine,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [QEC.Coding.BitTuring.DrainInput.tapes]
def partialExec (xs:List ℕ) (hx:xs.length=n+1) (s:List Bool):
    EvalsToInTime (TM2.step (FieldProjection.machine n keep).program)
      ((FieldProjection.machine n keep).init (stream xs++s))
      (some (QEC.Coding.BitTuring.DrainInput.partialHalt (FieldProjection.machine n keep) s (raw (fields n keep 0 xs))))
      (steps n keep xs) :=by
  refine ⟨⟨steps n keep xs,?_⟩,le_refl _⟩
  rw [←suffixHalt_eq]
  exact partial_run n keep xs hx s
def prefixMachine:=QEC.Coding.BitTuring.DrainInput.machine (FieldProjection.machine n keep)
def exec (xs:List ℕ) (hx:xs.length=n+1) (s:List Bool):
    EvalsToInTime (TM2.step (prefixMachine n keep).program) ((prefixMachine n keep).init (stream xs++s))
      (some ((prefixMachine n keep).halt (raw (fields n keep 0 xs)))) (steps n keep xs+s.length+1) :=
  QEC.Coding.BitTuring.DrainInput.executes (FieldProjection.machine n keep) (by change (0:Fin 3)≠2;decide) _ _ _ _ (partialExec n keep xs hx s)
noncomputable def time:Polynomial ℕ:=Polynomial.C 2*Polynomial.X+Polynomial.C 2
noncomputable def polyExec (xs:List ℕ) (hx:xs.length=n+1) (s:List Bool):
    EvalsToInTime (TM2.step (prefixMachine n keep).program) ((prefixMachine n keep).init (stream xs++s))
      (some ((prefixMachine n keep).halt (raw (fields n keep 0 xs)))) (time.eval (stream xs++s).length) :=by
  have h:=exec n keep xs hx s
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  have hs:=steps_le n keep xs
  simp only [time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,List.length_append]
  omega
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (n:ℕ) (keep:Fin (n+1)→Bool)
def Input:Type:=FieldProjection.Input n × List Bool
def input (x:Input n):List Bool:=stream x.1.val++x.2
noncomputable def computableInPolyTime:
    TM2ComputableInPolyTime (input n) id (fun x:Input n=>raw (fields n keep 0 x.1.val)) where
  tm:=(prefixMachine n keep).toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=time
  outputsFun:=fun x=>by
    change TM2OutputsInTime (prefixMachine n keep).toFinTM2 (List.map id (input n x))
      (some (List.map id (raw (fields n keep 0 x.1.val)))) (time.eval (input n x).length)
    have h:=Machine.outputsInTime (prefixMachine n keep) _ _ _ (polyExec n keep x.1.val x.1.property x.2)
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,input] using h
def allMask:Fin (n+1)→Bool:=fun _=>true
end QEC.Coding.BitTuring.UnaryArithmetic.PrefixProjection


