-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_BitDelimiters
-- name    : QEC_Coding_BitTuring_BitDelimiters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:03:14.328723+00:00
-- url     : https://prove2.me/theorems/4f24eceb-7bde-403c-8b7a-8b0508cf770f
-- title:
--   Bit Delimiters
-- statement:
--   Definitions and structural lemmas for Bit Delimiters, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/BitDelimiters.lean

import Definitions.Def_QEC_Coding_BitTuring_Composition
set_option autoImplicit false
namespace QEC.Coding.BitTuring.BitDelimiter
open Turing StateTransition
abbrev Label := Unit⊕Bool
abbrev Statement := TM2.Stmt (fun _:Fin 3=>Bool) Label (Option Bool)
def program : Label→Statement
  | .inl _=>.push 2 (fun _=>false) (.goto fun _=>.inr true)
  | .inr l=>liftStatement id Sum.inr id (fun _ w=>w) none (copyProgram l)
def machine : Machine where
  K:=Fin 3;input:=0;output:=2;Λ:=Label;main:=.inl ();σ:=Option Bool;initial:=none;program:=program
def embed : TM2.Cfg (fun _:Fin 3=>Bool) Bool (Option Bool)→
    TM2.Cfg (fun _:Fin 3=>Bool) Label (Option Bool) := liftCfg Sum.inr id id none
theorem stepAuxCopy (l:Bool) (v:Option Bool) (S:Fin 3→List Bool) :
    TM2.stepAux (program (.inr l)) v S=embed (TM2.stepAux (copyProgram l) v S) :=
  stepAux_liftStatement (K:=Fin 3) (K':=Fin 3) (Λ:=Bool) (Λ':=Label)
    (σ:=Option Bool) (σ':=Option Bool) id Sum.inr id (fun _ w=>w) none id id
    (fun _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl) (fun _ _ _=>rfl) (copyProgram l) v S
theorem stepCopy (c c':TM2.Cfg (fun _:Fin 3=>Bool) Bool (Option Bool))
    (h:TM2.step copyProgram c=some c') : TM2.step program (embed c)=some (embed c') := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none=>simp [TM2.step] at h
  | some l=>
    have hh:TM2.stepAux (copyProgram l) v S=c':=Option.some.inj h
    rw [←hh];exact congrArg some (stepAuxCopy l v S)
def startCfg (w:List Bool) : TM2.Cfg (fun _:Fin 3=>Bool) Label (Option Bool) :=
  ⟨some (.inl ()),none,![w,[],[]]⟩
theorem init_eq (w:List Bool) : machine.init w=startCfg w := by
  simp [Machine.init,machine,startCfg,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem header (w:List Bool) : TM2.step program (startCfg w)=
    some (embed (copyCfg true w [] [false] none)) := by
  simp [program,startCfg,embed,liftCfg,copyCfg,TM2.step,TM2.stepAux,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem halt_eq (y:List Bool) : embed (copyHalt y)=machine.halt y := by
  simp [embed,liftCfg,copyHalt,Machine.halt,machine,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
def exec (w:List Bool) : EvalsToInTime (TM2.step machine.program) (machine.init w)
    (some (machine.halt (w++[false]))) (2*w.length+3) := by
  have hc:(fun c=>c.bind (TM2.step copyProgram))^[2*w.length+2]
      (some (copyCfg true w [] [false] none))=some (copyHalt (w++[false])) := by
    rw [show 2*w.length+2=(w.reverse.length+1)+(w.length+1) by simp;omega,
      Function.iterate_add_apply,copyRun_source]
    simp only [List.append_nil]
    rw [copyRun_buffer,List.reverse_reverse]
  refine ⟨⟨2*w.length+3,?_⟩,le_refl _⟩
  rw [init_eq]
  change (fun c=>c.bind (TM2.step program))^[2*w.length+3] (some (startCfg w))=_
  rw [show 2*w.length+3=(2*w.length+2)+1 by omega,Function.iterate_add_apply]
  simp only [Function.iterate_one,Option.bind_some]
  rw [header]
  have h:=iterate_lift (TM2.step copyProgram) (TM2.step program) embed stepCopy _ _ _ hc
  rw [halt_eq] at h;exact h
end QEC.Coding.BitTuring.BitDelimiter
namespace QEC.Coding.BitTuring.BitReverse
open Turing StateTransition
def machine : Machine where
  K:=Fin 3;input:=1;output:=2;Λ:=Bool;main:=false;σ:=Option Bool;initial:=none;program:=copyProgram
theorem init_eq (w:List Bool) : machine.init w=copyCfg false [] w [] none := by
  simp [Machine.init,machine,copyCfg,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
theorem halt_eq (y:List Bool) : copyHalt y=machine.halt y := by
  simp [Machine.halt,machine,copyHalt,TM2.Cfg.mk.injEq]
  funext k;fin_cases k <;> simp [Function.update]
def exec (w:List Bool) : EvalsToInTime (TM2.step machine.program) (machine.init w)
    (some (machine.halt w.reverse)) (w.length+1) := by
  have h:=copyRun_buffer w [] none
  rw [List.append_nil,halt_eq,←init_eq] at h
  exact ⟨⟨w.length+1,h⟩,le_refl _⟩
end QEC.Coding.BitTuring.BitReverse


