-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryModularNegation
-- name    : QEC_Coding_BitTuring_UnaryModularNegation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:07:43.9592+00:00
-- url     : https://prove2.me/theorems/241c7278-9d70-4b11-bc3d-8951eafdbb46
-- title:
--   Unary Modular Negation
-- statement:
--   Definitions and structural lemmas for Unary Modular Negation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularNegation.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Mathlib.Data.ZMod.Basic
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FactorTest_halt_eq

set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularNegation
open Turing StateTransition
abbrev Var := Option Bool×Bool
abbrev Statement := TM2.Stmt (fun _:Fin 4=>Bool) (Fin 5) Var
def reset : Var := (none,false)
def program : Fin 5→Statement
  | 0=>.pop 0 (fun v h=>(h,v.2)) (.branch (fun v=>v.1.getD false)
      (.push 1 (fun _=>true) (.load (fun v=>(v.1,true)) (.goto fun _=>0))) (.goto fun _=>1))
  | 1=>.pop 0 (fun v h=>(h,v.2)) (.branch (fun v=>v.1.isSome)
      (.push 2 (fun _=>true) (.goto fun _=>1))
      (.load (fun v=>(none,v.2)) (.branch (fun v=>v.2) (.goto fun _=>2) (.goto fun _=>4))))
  | 2=>.pop 1 (fun v h=>(h,v.2)) (.branch (fun v=>v.1.isSome)
      (.pop 2 (fun v _=>(none,v.2)) (.goto fun _=>2)) (.goto fun _=>3))
  | 3=>.pop 2 (fun v h=>(h,v.2)) (.branch (fun v=>v.1.isSome)
      (.push 3 (fun _=>true) (.goto fun _=>3)) (.load (fun _=>reset) .halt))
  | _=>.pop 2 (fun v h=>(h,v.2)) (.branch (fun v=>v.1.isSome)
      (.goto fun _=>4) (.load (fun _=>reset) .halt))
def machine : Machine where
  K:=Fin 4;input:=0;output:=3;Λ:=Fin 5;main:=0;σ:=Var;initial:=reset;program:=program
def cfg (l:Fin 5) (s a q d:List Bool) (v:Var) :
    TM2.Cfg (fun _:Fin 4=>Bool) (Fin 5) Var := ⟨some l,v,![s,a,q,d]⟩
def halt (d:List Bool) : TM2.Cfg (fun _:Fin 4=>Bool) (Fin 5) Var :=
  ⟨none,reset,![[],[],[],d]⟩
theorem parseA_cons (s a q d:List Bool) (v:Var) :
    TM2.step program (cfg 0 (true::s) a q d v)=some (cfg 0 s (true::a) q d (some true,true)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem parseA_sep (s a q d:List Bool) (v:Var) :
    TM2.step program (cfg 0 (false::s) a q d v)=some (cfg 1 s a q d (some false,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem parseQ_cons (s a q d:List Bool) (v:Var) :
    TM2.step program (cfg 1 (true::s) a q d v)=some (cfg 1 s a (true::q) d (some true,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem parseQ_nil (a q d:List Bool) (v:Var) :
    TM2.step program (cfg 1 [] a q d v)=some (cfg (if v.2 then 2 else 4) [] a q d (none,v.2)) := by
  cases hv:v.2 <;> simp [TM2.step,program,cfg,TM2.stepAux,hv,TM2.Cfg.mk.injEq]
theorem cancel_cons (a q d:List Bool) (v:Var) :
    TM2.step program (cfg 2 [] (true::a) (true::q) d v)=some (cfg 2 [] a q d (none,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem cancel_nil (q d:List Bool) (v:Var) :
    TM2.step program (cfg 2 [] [] q d v)=some (cfg 3 [] [] q d (none,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
theorem copy_cons (q d:List Bool) (v:Var) :
    TM2.step program (cfg 3 [] [] (true::q) d v)=some (cfg 3 [] [] q (true::d) (some true,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem copy_nil (d:List Bool) (v:Var) :
    TM2.step program (cfg 3 [] [] [] d v)=some (halt d) := by
  simp [TM2.step,program,cfg,halt,reset,TM2.stepAux,TM2.Cfg.mk.injEq]
theorem drain_cons (q d:List Bool) (v:Var) :
    TM2.step program (cfg 4 [] [] (true::q) d v)=some (cfg 4 [] [] q d (some true,v.2)) := by
  simp [TM2.step,program,cfg,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem drain_nil (d:List Bool) (v:Var) :
    TM2.step program (cfg 4 [] [] [] d v)=some (halt d) := by
  simp [TM2.step,program,cfg,halt,reset,TM2.stepAux,TM2.Cfg.mk.injEq]
theorem runA (a:ℕ) (s b q d:List Bool) (v:Var) :
    (fun c=>c.bind (TM2.step program))^[a+1]
      (some (cfg 0 (unary a++false::s) b q d v))=
      some (cfg 1 s (unary a++b) q d (some false,v.2 || decide (0<a))) := by
  induction a generalizing b v with
  | zero=>simp [unary,parseA_sep]
  | succ a ih=>
    simp only [unary_succ,List.cons_append]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,parseA_cons]
    rw [ih];simp [unary_append_cons]
theorem runQ (q:ℕ) (a b d:List Bool) (v:Var) :
    (fun c=>c.bind (TM2.step program))^[q+1]
      (some (cfg 1 (unary q) a b d v))=
      some (cfg (if v.2 then 2 else 4) [] a (unary q++b) d (none,v.2)) := by
  induction q generalizing b v with
  | zero=>simp [unary,parseQ_nil]
  | succ q ih=>
    simp only [unary_succ]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,parseQ_cons]
    rw [ih];simp [unary_append_cons]
theorem runCancel (a r:ℕ) (d:List Bool) (v:Var) :
    (fun c=>c.bind (TM2.step program))^[a+1]
      (some (cfg 2 [] (unary a) (unary (a+r)) d v))=
      some (cfg 3 [] [] (unary r) d (none,v.2)) := by
  induction a generalizing v with
  | zero=>simp [unary,cancel_nil]
  | succ a ih=>
    rw [show a+1+r=(a+r)+1 by omega]
    simp only [unary_succ]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,cancel_cons]
    exact ih (none,v.2)
theorem runCopy (q:ℕ) (d:List Bool) (v:Var) :
    (fun c=>c.bind (TM2.step program))^[q+1]
      (some (cfg 3 [] [] (unary q) d v))=some (halt (unary q++d)) := by
  induction q generalizing d v with
  | zero=>simp [unary,copy_nil]
  | succ q ih=>
    simp only [unary_succ]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,copy_cons]
    rw [ih];simp [unary_append_cons]
theorem runDrain (q:ℕ) (d:List Bool) (v:Var) :
    (fun c=>c.bind (TM2.step program))^[q+1]
      (some (cfg 4 [] [] (unary q) d v))=some (halt d) := by
  induction q generalizing v with
  | zero=>simp [unary,drain_nil]
  | succ q ih=>
    simp only [unary_succ]
    rw [Function.iterate_succ_apply]
    simp only [Option.bind_some,drain_cons]
    exact ih (some true,v.2)
theorem parseRun (a q:ℕ) :
    (fun c=>c.bind (TM2.step program))^[a+q+2]
      (some (cfg 0 (pairInput a q) [] [] [] reset))=
      some (cfg (if decide (0<a) then 2 else 4) [] (unary a) (unary q) [] (none,decide (0<a))) := by
  rw [show a+q+2=(q+1)+(a+1) by omega,Function.iterate_add_apply]
  simp only [pairInput]
  rw [runA]
  simp only [reset,Bool.false_or,List.append_nil]
  simpa only [List.append_nil] using runQ q (unary a) [] [] (some false,decide (0<a))
def output (a q:ℕ) : ℕ := if a=0 then 0 else q-a
def steps (a q:ℕ) : ℕ := if a=0 then 2*q+3 else a+2*q+4
theorem init_eq (a q:ℕ) : machine.init (pairInput a q)=cfg 0 (pairInput a q) [] [] [] reset := by
  simp [Machine.init,machine,cfg,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem halt_eq (y:List Bool) : halt y=machine.halt y := by
  simp [halt,Machine.halt,machine,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem run (a q:ℕ) (haq:a≤q) :
    (fun c=>c.bind (TM2.step machine.program))^[steps a q]
      (some (machine.init (pairInput a q)))=some (machine.halt (unary (output a q))) := by
  rw [init_eq,←halt_eq]
  change (fun c=>c.bind (TM2.step program))^[steps a q]
    (some (cfg 0 (pairInput a q) [] [] [] reset))=_
  by_cases ha:a=0
  · subst a
    rw [show steps 0 q=(q+1)+(0+q+2) by simp only [steps,↓reduceIte];omega,
      Function.iterate_add_apply,parseRun]
    simp only [Nat.lt_irrefl,decide_false,Bool.false_eq_true,↓reduceIte,unary_zero]
    rw [runDrain]
    simp [output,unary]
    rfl
  · have hap:0<a:=by omega
    rw [show steps a q=((q-a+1)+(a+1))+(a+q+2) by simp only [steps,ha,↓reduceIte];omega,
      Function.iterate_add_apply,parseRun]
    simp only [hap,decide_true,↓reduceIte]
    rw [Function.iterate_add_apply]
    have hqa:q=a+(q-a):=by omega
    have hc:=runCancel a (q-a) [] (none,true)
    rw [←hqa] at hc
    rw [hc,runCopy]
    simp [output,ha]
    rfl
def exec (a q:ℕ) (haq:a≤q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (pairInput a q))
      (some (machine.halt (unary (output a q)))) (steps a q) :=
  ⟨⟨steps a q,run a q haq⟩,le_refl _⟩
theorem steps_le (a q:ℕ) : steps a q≤3*((pairInput a q).length+1) := by
  rw [pairInput_length]
  by_cases ha:a=0 <;> simp only [steps,ha,↓reduceIte] <;> omega
noncomputable def time : Polynomial ℕ := Polynomial.C 3*(Polynomial.X+1)
noncomputable def polyExec (a q:ℕ) (haq:a≤q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (pairInput a q))
      (some (machine.halt (unary (output a q)))) (time.eval (pairInput a q).length) := by
  have h:=exec a q haq
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  simpa [time] using steps_le a q
theorem output_eq_neg (a q:ℕ) (hq:0<q) (haq:a<q) : output a q=(-(a:ZMod q)).val := by
  let : NeZero q:=⟨hq.ne'⟩
  have he:((a:ZMod q)=0)↔a=0 := by
    rw [←ZMod.val_eq_zero (a:ZMod q),ZMod.val_natCast_of_lt haq]
  simp only [output,ZMod.neg_val,he,ZMod.val_natCast_of_lt haq]
noncomputable def outputsInTime (a q:ℕ) (haq:a≤q) :
    TM2OutputsInTime machine.toFinTM2 (pairInput a q) (some (unary (output a q)))
      (time.eval (pairInput a q).length) := Machine.outputsInTime machine _ _ _ (polyExec a q haq)
noncomputable def outputsZModInTime (a q:ℕ) (hq:0<q) (haq:a<q) :
    TM2OutputsInTime machine.toFinTM2 (pairInput a q) (some (unary (-(a:ZMod q)).val))
      (time.eval (pairInput a q).length) := by
  have h:=outputsInTime a q haq.le
  rw [output_eq_neg a q hq haq] at h;exact h
def Domain := {x:ℕ×ℕ+//x.1<x.2.val}
def input (x:Domain) := pairInput x.val.1 x.val.2.val
noncomputable def computableInPolyTime : TM2ComputableInPolyTime input unary
    (fun x:Domain=>output x.val.1 x.val.2.val) where
  tm:=machine.toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=time
  outputsFun:=fun x=>by
    change TM2OutputsInTime machine.toFinTM2 (List.map id (input x))
      (some (List.map id (unary (output x.val.1 x.val.2.val)))) (time.eval (input x).length)
    have h:=outputsInTime x.val.1 x.val.2.val x.property.le
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,input] using h
end QEC.Coding.BitTuring.UnaryArithmetic.ModularNegation


